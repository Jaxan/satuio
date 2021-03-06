"""
Script for finding AD sequences in a Mealy machine. Uses SAT solvers
(in pysat) to search efficiently. The length of the sequence is fixed,
but you specify multiple the states for which the ADS is supposed to
work. When an ADS does not exist, the solver returns UNSAT. For the
usage, please run

  python3 ads.py --help

Note: it is not advised to construct an ADS for the whole machine
in this way. The encoding takes a very long time, and the solver
will have a hard time. Use the algorithm by Lee and Yannakakis
instead (the ADS-problem for the whole state space is in P).

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
import random


# We set up some things for nice output
console = Console(highlight=False)


# *****************
# Reading the input
# *****************

# command line options
parser = ArgumentParser()
parser.add_argument('filename', help='File of the mealy machine (dot format)')
parser.add_argument('length', help='Length of the ADS', type=int)
parser.add_argument('-v', '--verbose', help='Show more output', action='store_true')
parser.add_argument('--show-differences', help='Show even more output', action='store_true')
parser.add_argument('--random-base', help='Chooses a random base', action='store_true')
parser.add_argument('--base-size', type=int)
parser.add_argument('--solver', help='Which solver to use (default g3)', default='g3')
parser.add_argument('--states', help='For which states to compute an ADS', nargs='+')
args = parser.parse_args()

# reading the automaton
(alphabet, outputs, all_states, delta, labda) = read_machine(args.filename)
states = args.states
length = args.length

if args.random_base and args.base_size > 1:
  states = random.sample(all_states, k=args.base_size)
elif len(args.states) > 1:
  states = args.states
else:
  raise ValueError('Should specify at least 2 states')

console.print(now(), f'Constructed automaton with [bold blue]{len(all_states)} states[/bold blue], [bold green]{len(alphabet)} symbols[/bold green] and Q_0 has [bold blue]{len(states)} states[/bold blue]')


# ********************
# Seting up the solver
#  And the variables
# ********************

vpool = IDPool()
solver = Solver(name=args.solver)

# Since the solver can only deal with variables x_i, we need
# a mapping of variabeles: x_whatever  ->  x_i.
# We use the IDPool of pysat for this. It generates variables
# on the fly.
def var(x):
  return(vpool.id(('uio', x)))

# Each state has its own path, and on this path we encode
# the states, the input, and the output.
# avar(s, i, a) means: on path s, on place i there is symbol a
def avar(s, i, a):
  return var(('a', s, i, a))

# svar(s, i, t) means: on path s, at place i, we are in state t
def svar(s, i, t):
  return var(('s', s, i, t))

# ovar(s, i, o) means: on path s, on place i, there is output o
def ovar(s, i, o):
  return var(('o', s, i, o))

# We use extra variables to encode the fact that there is
# a difference in output (a la Tseytin transformation)
# dvar(s, t, i) means: the paths s and t differ on place i.
def dvar(s, t, i):
  return var(('d1', s, t, i))

# Since we are looking for an adaptive distinguishing sequence,
# the inputs must be consistent among the paths, until there is
# a difference. We use additional variables for that
# d2var(s, t, i) means: the paths s and t differ on i or earlier
def d2var(s, t, i):
  return var(('d2', s, t, i))

# We often need to assert that exacly one variable in a list holds.
# For that we use pysat's cardinality encoding. This might introduce
# additional variables. But that does not matter for us.
def unique(lits):
  cnf = CardEnc.equals(lits, 1, vpool=vpool, encoding=EncType.seqcounter)
  solver.append_formula(cnf.clauses)

console.print(now(), f'Solver {args.solver} ready for clauses')


# ********************
# Constructing the CNF
# ********************


# For each state s, we construct a path of possible successor states,
# following the guessed words. This path should be consistent with delta,
# and we also record the outputs along this path. The outputs are later
# used to decide whether we found a different output.
possible_outputs = {}
possible_states = {}
for s in tqdm(states, desc="CNF paths", leave=False):
  # current set of possible states we're in
  current_set = set([s])
  # set of successors for the next iteration of i
  next_set = set()

  for i in range(length):
    # Only one input at this position
    unique([avar(s, i, a) for a in alphabet])

    # Only one successor state should be enabled.
    # For i == 0, this is a single state (s).
    unique([svar(s, i, t) for t in current_set])

    # We keep track of the possible outputs and states
    possible_outputs[(s, i)] = set()
    possible_states[(s, i)] = current_set

    for t in current_set:
      for a in alphabet:
        output = labda[(t, a)]
        possible_outputs[(s, i)].add(output)

        # Constraint: on path s, when in state t and input a, we output o
        # x_('s', s, i, t) /\ x_('in', s, i, a) => x_('o', i, labda(t, a))
        # == -x_('s', s, i, t) \/ -x_('in', s, i, a) \/ x_('o', i, labda(t, a))
        solver.add_clause([-svar(s, i, t), -avar(s, i, a), ovar(s, i, output)])

        # when i == length-1 we don't need to consider successors
        if i < length-1:
          next_t = delta[(t, a)]
          next_set.add(next_t)

          # Constraint: on path s, when in state t and input a, we go to next_t
          # x_('s', s, i, t) /\ x_('in', s, i, a) => x_('s', s, i+1, delta(t, a))
          # == -x_('s', s, i, t) \/ -x_('in', s, i, a) \/ x_('s', s, i+1, delta(t, a))
          solver.add_clause([-svar(s, i, t), -avar(s, i, a), svar(s, i+1, next_t)])

    # Only one output should be enabled
    unique([ovar(s, i, o) for o in possible_outputs[(s, i)]])

    # Next iteration with successor states
    current_set = next_set
    next_set = set()


# Now we will encode differences in outputs (and equal inputs, as
# long as there is no difference).
for s in tqdm(states, desc="CNF diffs", leave=False):
  for t in states:
    # We skip s == t, since those state are equivalent.
    # I am not sure whether we can skip s <= t, since our construction
    # below is not symmetrical. We do however include a clause which
    # states that the dvars are symmetrical. This should help the
    # solver a little bit.
    if s == t:
      continue

    # First, we require that there is a difference on the paths of s and t
    solver.add_clause([dvar(s, t, i) for i in range(length)])

    for i in range(length):
      # The difference variables are symmetric in the sense that
      # x_('d', s, t, i) <=> x_('d', t, s, i)
      # We do only one direction here, the other direction is handled
      # with s and t swapped. I don't know whether this is needed though.
      solver.add_clause([-dvar(s, t, i), dvar(t, s, i)])
      solver.add_clause([-d2var(s, t, i), d2var(t, s, i)])

      # First we encode that d2var is the closure of dvar.
      # Note that we only do one direction. Setting d2var to true helps the
      # solver, as it means that the inputs may be chosen differently.
      # So if the solver sets a d2var2 to true, it must mean there is
      # a difference, or an earlier difference.
      if i == 0:
        # d2var(s, t, 0) => dvar(s, t, 0) (there is no "earlier")
        solver.add_clause([-d2var(s, t, i), dvar(s, t, i)])
      else:
        # d2var(s, t, i) => (dvar(s, t, i) \/ d2var(s, t, i-1))
        solver.add_clause([-d2var(s, t, i), dvar(s, t, i), d2var(s, t, i-1)])

      # Now we encode that, if there is no difference yet, the
      # guessed inputs must be the same for both states.
      # -d2var(s, t, i) => (avar(s, i, a) <=> avar(t, i, a))
      for a in alphabet:
        # for i == 0, the inputs have to be the same
        if i == 0:
          # avar(s, i, a) => avar(t, i, a)
          solver.add_clause([-avar(s, i, a), avar(t, i, a)])
        else:
          # We do one direction -d2var(s, t, i-1) /\ avar(s, i, a) => avar(t, i, a)
          solver.add_clause([d2var(s, t, i-1), -avar(s, i, a), avar(t, i, a)])

      # Also, if there is no difference yet, the successor states must
      # be different. (If they collapse, no difference can ever occur.)
      # This is not strictly necessary as a clause, but it makes the
      # solving much faster.
      # -d2var(s, t, i-1) /\ svar(s, i, s2) => -svar(t, i, s2)
      if i > 0:
        for s2 in possible_states[(s, i)]:
          if s2 in possible_states[(t, i)]:
            solver.add_clause([d2var(s, t, i-1), -svar(s, i, s2), -svar(t, i, s2)])

      # We encode: if there is a difference, then the outputs should
      # actually differ. (We do not have to encode the other implication!)
      # x_('d', s, t, i) /\ x_('o', s, i, o) => -x_('o', t, i, o)
      # Note: when o is not possible for state t, then the clause already holds
      outputs_s = possible_outputs[(s, i)]
      outputs_t = possible_outputs[(t, i)]
      for o in outputs_s:
        if o in outputs_t:
          solver.add_clause([-dvar(s, t, i), -ovar(s, i, o), -ovar(t, i, o)])


console.print(now(), f'Constructed CNF with {solver.nof_clauses()} clauses and {solver.nof_vars()} variables')


# ******************
# Solving and output
# ******************

# We set up some things for nice output
max_state_length = max([len(str) for str in states])

# Solve it!
solution = solver.solve()
console.print(now(), 'Solver finished')

# If there is no solution, we can exit. As far as I know
# there is no relevant information in the "core", as there
# are no assumptions used in our encoding.
if not solution:
  console.print('! no ADS of length', length, style='bold red')
  console.print(now(), 'Done')
  exit()

# Get the set of true variables
truth = get_truth(solver)

# (If verbose) For each state, we print the paths and output.
# We mark the differences red (there can be differences not
# marked, these are the differences decided in the solving).
if args.verbose:
  console.print('! words:')

  # Print the words for each state. Note that these are
  # also UIO sequenes for that state.
  for s in states:
    console.print(s.rjust(max_state_length, ' '), end=': ', style='bold black')

    for i in range(length):
      for a in alphabet:
        if avar(s, i, a) in truth:
          console.print(a, end=' ', style='bold green')
    console.print('')

  # Print the complete path of each state
  console.print('! paths')
  for s in states:
    console.print(s.rjust(max_state_length, ' '), end=': ', style='bold black')
    for i in range(length):
      for t in possible_states[(s, i)]:
        if svar(s, i, t) in truth:
          console.print(t, end=' ', style='blue')

      for a in alphabet:
        if avar(s, i, a) in truth:
          console.print(a, end=' ', style='green')

      for o in possible_outputs[(s, i)]:
        if ovar(s, i, o) in truth:
          console.print(o, end=' ', style='red')

    console.print('')

# Print even more debugging info (not recommended)
if args.show_differences:
  console.print('! differences')
  for s in states:
    for t in states:
      console.print(s, 'vs', t, end=': ')
      for i in range(length):
        if dvar(s, t, i) in truth:
          console.print('X', end='')
        else:
          console.print('.', end='')

        if d2var(s, t, i) in truth:
          console.print('-', end=' ')
        else:
          console.print('_', end=' ')

      console.print('')


# Now we will extract the tree from the solution above.
# The initial_set indicates which states we possibly started at,
# and the level is the current depth of the tree.
def extract_tree(initial_set, level):
  global truth, possible_outputs

  some_state = some_elem(initial_set)

  # If there is only one state left, we can stop the tree here
  if len(initial_set) == 1:
    return { 'leaf': some_state }

  # Get the (single) input which makes the split
  split_symbol = some_elem([a for a in alphabet if avar(some_state, level, a) in truth])

  # Collect the different outputs, put them in buckets
  split_outputs = {}
  for s in initial_set:
    for o in possible_outputs[(s, level)]:
      if ovar(s, level, o) in truth:
        if o not in split_outputs:
          split_outputs[o] = []
        split_outputs[o].append(s)
        break

  # For each bucket, recursively create the tree
  sub_trees = {}
  for (o, xs) in split_outputs.items():
    sub_trees[o] = extract_tree(xs, level + 1)

  # Return a node
  return { 'split_symbol': split_symbol, 'subtree': sub_trees }


# Pretty (and compactly) printing the tree. As before, we color code
# the output: green for inputs, red for outputs, and blue for states
def print_tree(console, tree, left=''):
  # The leaf is inlined in the printing
  if 'leaf' in tree:
    console.print(f'> state [bold blue]{tree["leaf"]}[/bold blue]')
  else:
    # The next input symbol is also inlined
    console.print(f'> [bold green]{tree["split_symbol"]}[/bold green]', end='')
    # We contract single-successor paths in the tree
    while len(tree['subtree']) == 1:
      tree = some_elem(tree['subtree'].values())
      console.print(f' - [bold green]{tree["split_symbol"]}[/bold green]', end='')
    else:
      console.print()
      counter = len(tree['subtree'])
      # Each possible output gets a new line, and we recurse
      for (o, subtree) in tree['subtree'].items():
        str_elm, str_pad = '├─ ', '│  '
        counter -= 1
        if counter == 0:
          str_elm, str_pad = '└─ ', '   '
        console.print(left, str_elm, end='', sep='')
        console.print(o, end=' ', style='bold red')
        print_tree(console, subtree, left + str_pad)


# Output the distinguishing tree
print_tree(console, extract_tree(states, 0))
print('')

# Report some final stats
console.print(now(), 'Done')


# TODO: we know that dvar(s, t, i) is an equivalence relation for
# each i. Do we help the solver when asserting that? Or will that
# make the solving slower? One problem: transitivity requires n^3
# many clauses... (Symmetry is already implemented.)

# TODO: try to see whether the other implication of d2var -> d2var
# makes the solving more efficient. The clauses are redundant, but
# it might help. It also makes sure that enumerating several models
# are actually different ADSs.

# TODO: the same for difference -> dvar. We only do one implication,
# and perhaps adding the other makes it faster.
