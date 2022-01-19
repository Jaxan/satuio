"""
Script for finding UIO sequences in a Mealy machine. Uses SAT solvers
(in pysat) to search efficiently. The length of the sequence is fixed,
but you can specify multiple (or all) states for which an UIO is
desired. When an UIO (of specified length) does not exist, the solver
returns UNSAT. For the usage, please run
  
  python3 uio.py --help

© Joshua Moerman, Open Universiteit, 2022
"""

# Import the solvers and utilities
from pysat.solvers import Solver
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType

from argparse import ArgumentParser # Command line options
from rich.console import Console    # Import colorized output
from time import time               # Time for rough timing measurements
from tqdm import tqdm               # Import fancy progress bars

from parser import read_machine

# function for some time logging
start = time()
start_total = start
def measure_time(*str):
  global start
  now = time()
  print('***', *str, "in %.3f seconds" % (now - start))
  start = now


# *****************
# Reading the input
# *****************

# command line options
parser = ArgumentParser()
parser.add_argument('filename', help='File of the mealy machine (dot format)')
parser.add_argument('length', help='Length of the UIO', type=int)
parser.add_argument('-v', '--verbose', help="Show more output", action='store_true')
parser.add_argument('--solver', help='Which solver to use (default g3)', default='g3')
parser.add_argument('--bases', help='For which states to compute an UIO (leave empty for all states)', nargs='*')
args = parser.parse_args()

# reading the automaton
(alphabet, outputs, states, delta, labda) = read_machine(args.filename)

# if the base states are not specified, take all
if args.bases == None:
  bases = states
else:
  bases = args.bases

length = args.length

measure_time('Constructed automaton with', len(states), 'states and', len(alphabet), 'symbols')


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

measure_time('Setup solver', args.solver)


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
for s in tqdm(states, desc="CNF paths"):
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
for s in tqdm(states, desc="CNF diffs"):
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

measure_time('Constructed CNF with', solver.nof_clauses(), 'clauses and', solver.nof_vars(), 'variables')


# ******************
# Solving and output
# ******************

# We set up some things for nice output
console = Console(markup=False, highlight=False)
max_state_length = max([len(str) for str in states])

# We count the number of uios
num_uios = {True: 0, False: 0}

# We want to find an UIO for each base. We have already constructed
# the CNF. So it remains to add assumptions to the solver, this is
# called "incremental solving" in SAT literature.
for base in bases:
  console.print('')
  console.print('*** UIO for state', base, style='bold blue')

  # Solve with bvar(base) being true
  b = solver.solve(assumptions=[bvar(base)])
  num_uios[b] = num_uios[b] + 1
  measure_time('Solver finished')

  if b:
    # We get the model, and store all true variables
    # in a set, for easy lookup.
    m = solver.get_model()
    truth = set()
    for l in m:
      if l > 0:
        truth.add(l)
    
    # We print the word
    console.print('! UIO of length', length, style='bold green')
    for i in range(length):
      for a in alphabet:
        if avar(i, a) in truth:
          console.print(a, end=' ', style='bold green')
    console.print('')

    # (If verbose) For each state, we print the paths and output.
    # We mark the differences red (there can be differences not
    # marked, these are the differences decided in the solving).
    if args.verbose:
      console.print('! paths')
      for s in states:
        console.print(s.rjust(max_state_length, ' '), ' ==> ', end=' ')
        for i in range(length):
          for t in states:
            if svar(s, i, t) in truth:
              console.print(t, end=' ')

          for o in possible_outputs[(s, i)]:
            if ovar(s, i, o) in truth:
              style = ''
              if s == base:
                style = 'bold green'
              elif evar(s, i) in truth:
                style = 'bold red'
              
              console.print(o, end=',  ', style=style)
        console.print('')

  else:
    console.print('! no UIO of length', length, style='bold red')
    # The core returned by the solver is not interesting:
    # It is only the assumption (i.e. bvar).


# Report some final stats
start = start_total
print('')
measure_time("Done with total time")
print('With UIO:', num_uios[True])
print('without: ', num_uios[False])
