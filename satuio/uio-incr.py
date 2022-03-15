"""
Script for finding UIO sequences in a Mealy machine. Uses SAT solvers
(in pysat) to search efficiently. The length is incremented each
iteration, so that short UIOs are found fast. It also uses simple
techniques to extend UIOs to more states if an UIO is found. This
can result in UIOs which are longer than the specified bound. For
the usage, please run

  python3 uio-incr.py --help

If you want to read this script, my suggestion is to first read
and understand uio.py. That file is simpler and perhaps better
structured.

© Joshua Moerman, Open Universiteit, 2022
"""

# Import the solvers and utilities
from pysat.solvers import Solver
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType

from argparse import ArgumentParser # Command line options
from rich.console import Console    # Import colorized output
from tqdm import tqdm               # Import fancy progress bars

from utils.parser import read_machine
from utils.utils import *


# We set up some things for nice output
console = Console(highlight=False)


# *****************
# Reading the input
# *****************

# command line options
parser = ArgumentParser()
parser.add_argument('filename', help='File of the mealy machine (dot format)')
parser.add_argument('--bound', help='Upper bound (incl.) for the UIO solving', type=int)
parser.add_argument('--time', help='Upper bound on search time (ms)', type=int)
parser.add_argument('--solver', help='Which solver to use (default g3)', default='g3')
parser.add_argument('--bases', help='For which states to compute an UIO (leave empty for all states)', nargs='*')
args = parser.parse_args()

# reading the automaton
(alphabet, outputs, states, delta, labda) = read_machine(args.filename)

# if the base states are not specified, take all
if args.bases == None:
  # Has to be a copy, because we will modify bases!
  bases = states.copy()
else:
  bases = args.bases

bound = args.bound

console.print(now(), f'Constructed automaton with [bold blue]{len(states)} states[/bold blue] and [bold green]{len(alphabet)} symbols[/bold green]')


# ****************
# UIO implications
#  And length = 1
# ****************

# We are going to look for transitions s --i/o--> t such that if
# t has an UIO, then automatically s has an UIO. For this, we need
# to consider the predecessors of t with unique input/output. We
# use a dictionary to sort this out.
# incoming :: state -> (input, output) -> [predecessor state]
incoming = {}

# And we are going to look for UIOs of length 1. Again we use a
# dictionary for this.
# (input, output) -> [origin state]
input_output_pairs = {}

for s in states:
  for i in alphabet:
    t = delta[(s, i)]
    o = labda[(s, i)]

    # First, we record input/output pair
    # for the UIOs of length = 1.
    if (i, o) not in input_output_pairs:
      input_output_pairs[(i, o)] = []

    input_output_pairs[(i, o)].append(s)

    # For predecessors, we can skip self-loops, because if t has
    # an UIO we already know that s = t has an UIO...
    if t == s:
      continue

    if t not in incoming:
      incoming[t] = {}

    if (i, o) not in incoming[t]:
      incoming[t][(i, o)] = []

    # Record predecessors of t
    incoming[t][(i, o)].append(s)

# Extract edges from `incoming`, if there is only a single
# state for the given input/output pair. We only store the
# input word, not the output, as we don't use it.
# uio_implication_graph :: state -> [(predecessor, input)]
uio_implication_graph = {}
for (s, m) in incoming.items():
  uio_implication_graph[s] = []
  for ((i, o), pred) in m.items():
    if len(pred) == 1:
      uio_implication_graph[s].append((pred[0], i))

incoming.clear()

# Extract unique input/output from the `input_output_pairs`.
# We only store the input word, as we don't use the output.
# new_uios :: state -> word
new_uios = {}
for ((i, o), ls) in input_output_pairs.items():
  if len(ls) == 1:
    new_uios[ls[0]] = [i]

input_output_pairs.clear()

# By using a bfs on the uio-implication-graph, we can extend known UIOs
# to other states. We define a function to do this. It operates on global
# variables. We do this now, for the length = 1 UIOs, but also after each
# iteration of the solver.
# uios :: state -> word
uios = {}
def extend(new_uios):
  global uios, bases
  queue = list(new_uios.items())

  while queue:
    (t, uio) = queue.pop(0)

    # If we already have an UIO for s, skip
    # (unless it is a smaller one)
    if t in uios and len(uio) >= len(uios[t]):
      continue

    # Store the UIO
    uios[t] = uio

    # We don't have to search anymore for t, so remove it
    if t in bases:
      bases.remove(t)

    # And follow the graph to extend to other states.
    # Note: these may not be the smallest UIO for that state.
    # But it is an UIO nevertheless.
    if t in uio_implication_graph:
      for (s, i) in uio_implication_graph[t]:
        queue.append((s, [i] + uio))

# We extend our 1-letter UIOs
extend(new_uios)
new_uios = {}

console.print(now(), f'Found [bold green]{len(uios)} simple uios[/bold green] already')


# ********************
# Seting up the solver
#  And the variables
# ********************

length = 2
while True:
  # Check the given bounds
  if args.bound and length > bound:
    break
  if args.time and time_since_start() * 1000 > args.time:
    break

  # If there are no more states for which we want an UIO,
  # we stop the search.
  if not bases:
    break

  new_uios = {}

  # Otherwise, we will setup a solver and search for them
  console.print(now(), f"> Solving for [bold red]length {length}[/bold red] for[bold blue] {len(bases)} states[/bold blue]")
  with Solver(name=args.solver) as solver:
    # Since the solver can only deal with variables x_i, we need
    # a mapping of variabeles: x_whatever  ->  x_i.
    # We use the IDPool of pysat for this. It generates variables
    # on the fly.
    vpool = IDPool()
    def var(x):
      return(vpool.id(('uio', x)))

    # Variables for the guessed word
    # avar(i, a) means: on place i there is symbol a
    def avar(i, a):
      return var(('a', i, a))

    # Each state has its own path, and on this path we encode
    # states and outputs
    # svar(s, i, t) means: on path s, at place i, we are in state t
    def svar(s, i, t):
      return var(('s', s, i, t))

    # ovar(s, i, o) means: on path s, on place i, there is output o
    def ovar(s, i, o):
      return var(('o', s, i, o))

    # We use extra variables to encode the fact that there is
    # a difference in output (a la Tseytin transformation)
    # evar(s, i) means: on path s, on place i, there is a difference
    # in output. Note: the converse (if there is a difference
    # evar(s, i) is true) does not hold!
    def evar(s, i):
      return var(('e', s, i))

    # In order to re-use parts of the formula, we introduce
    # enabling variables. These indicate the fixed state for which
    # we want to compute an UIO. By changing these variables only, we
    # can keep most of the formula the same and incrementally solve it.
    # The fixed state is called the "base".
    # bvar(s) means: s is the base.
    def bvar(s):
      return var(('base', s))

    # We often need to assert that exacly one variable in a list holds.
    # For that we use pysat's cardinality encoding. This might introduce
    # additional variables. But that does not matter for us.
    def unique(lits):
      cnf = CardEnc.equals(lits, 1, vpool=vpool, encoding=EncType.seqcounter)
      solver.append_formula(cnf.clauses)


    # ********************
    # Constructing the CNF
    # ********************

    # Guessing the word:
    for i in range(length):
      unique([avar(i, a) for a in alphabet])

    # We should only enable one base state.
    # (This allows for an optimisation later.)
    unique([bvar(base) for base in bases])


    # For each state s, we construct a path of possible successor states,
    # following the guessed word. This path should be consistent with delta,
    # and we also record the outputs along this path. The outputs are later
    # used to decide whether we found a different output.
    possible_outputs = {}
    for s in tqdm(states, desc="CNF paths", leave=False):
      # current set of possible states we're in
      current_set = set([s])
      # set of successors for the next iteration of i
      next_set = set()

      for i in range(length):
        # Only one successor state should be enabled.
        # For i == 0, this is a single state (s).
        unique([svar(s, i, t) for t in current_set])

        # We keep track of the possible outputs
        possible_outputs[(s, i)] = set()

        for t in current_set:
          sv = svar(s, i, t)

          for a in alphabet:
            av = avar(i, a)

            output = labda[(t, a)]
            possible_outputs[(s, i)].add(output)

            # Constraint: on path s, when in state t and input a, we output o
            # x_('s', s, i, t) /\ x_('in', i, a) => x_('o', i, labda(t, a))
            # == -x_('s', s, i, t) \/ -x_('in', i, a) \/ x_('o', i, labda(t, a))
            solver.add_clause([-sv, -av, ovar(s, i, output)])

            # when i == length-1 we don't need to consider successors
            if i < length-1:
              next_t = delta[(t, a)]
              next_set.add(next_t)

              # Constraint: on path s, when in state t and input a, we go to next_t
              # x_('s', s, i, t) /\ x_('in', i, a) => x_('s', s, i+1, delta(t, a))
              # == -x_('s', s, i, t) \/ -x_('in', i, a) \/ x_('s', s, i+1, delta(t, a))
              solver.add_clause([-sv, -av, svar(s, i+1, next_t)])

        # Only one output should be enabled
        unique([ovar(s, i, o) for o in possible_outputs[(s, i)]])

        # Next iteration with successor states
        current_set = next_set
        next_set = set()


    # If the output of a state is different than the one from our base state,
    # then, we encode that in a new variable. This is only needed when the base
    # state is active, so the first literal in these clauses is -bvar(base).
    # Also note, we only encode the converse: if there is a difference claimed
    # and base has a certain output, than the state should not have that output.
    # This means that the solver doesn't report all differences, but at least one.
    for s in tqdm(states, desc="CNF diffs", leave=False):
      # Constraint: there is a place, such that there is a difference in output
      # \/_i x_('e', s, i)
      # If s is our base, we don't care (this can be done, because only
      # a single bvar is true).
      if s in bases:
        solver.add_clause([bvar(s)] + [evar(s, i) for i in range(length)])
      else:
        solver.add_clause([evar(s, i) for i in range(length)])

      # Now we actually encode when the difference occurs
      for base in bases:
        if s == base:
          continue

        bv = bvar(base)

        for i in range(length):
          outputs_base = possible_outputs[(base, i)]
          outputs_s = possible_outputs[(s, i)]

          # We encode: if the base is enabled and there is a difference,
          # then the outputs should actually differ. (We do not have to
          # encode the other implication!)
          # x_('b', base) /\ x_('e', s, i) /\ x_('o', base, i, o) => -x_('o', s, i, o)
          # Note: when o is not possible for state s, then the clause already holds
          for o in outputs_base:
            if o in outputs_s:
              solver.add_clause([-bv, -evar(s, i), -ovar(base, i, o), -ovar(s, i, o)])

    console.print(now(), f'  > Constructed CNF with {solver.nof_clauses()} clauses and {solver.nof_vars()} variables, solving with {args.solver}')


    # ******************
    # Solving and output
    # ******************

    # We want to find an UIO for each base. We have already constructed
    # the CNF. So it remains to add assumptions to the solver, this is
    # called "incremental solving" in SAT literature.
    for base in tqdm(bases, desc='solving', leave=False):
      # If we run out of time, stop solving (but finish other stuff)
      if args.time and time_since_start() * 1000 > args.time:
        break

      # Solve with bvar(base) being true
      b = solver.solve(assumptions=[bvar(base)])

      # if there is no UIO, we go to the next state
      # we might find one later, with the length increased.
      if not b:
        continue

      # Get the set of true variables
      truth = get_truth(solver)

      # We extract the word
      uio = []
      for i in range(length):
        for a in alphabet:
          if avar(i, a) in truth:
            uio.append(a)

      new_uios[base] = uio

  # Getting some stats
  new_count = len(new_uios)
  curr_count = len(uios)

  # Extend with uio implication graph
  extend(new_uios)
  new_uios = {}

  # Print statistics
  tot_count = len(uios)
  console.print(now(), f'  > found {new_count} new uios, {tot_count - curr_count - new_count} extended, [bold green]total = {tot_count}[/bold green]')

  length = length + 1


for (s, uio) in uios.items():
  console.print(s, style='bold black', end=' => ')
  console.print(uio, style='bold green')
console.print('')

# Report some final stats
measure_total_time('\nDone')
console.print(f'uios found: {100*len(uios)/len(states):.0f}')
console.print(f'avg length: {sum([len(uio) for uio in uios.values()])/len(uios):.3}')
