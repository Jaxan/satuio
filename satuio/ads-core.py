"""
WIP script for returning the unsat core in the case an ADS does
*not* exist. This could be merged into the main ads script,
although there is an additional cost (presumably). Usage:

  python3 ads-core.py --help

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


# *****************
# Reading the input
# *****************

# command line options
parser = ArgumentParser()
parser.add_argument('filename', help='File of the mealy machine (dot format)')
parser.add_argument('length', help='Length of the ADS', type=int)
parser.add_argument('--solver', help='Which solver to use (default g3)', default='g3')
parser.add_argument('--states', help='For which states to compute an ADS', nargs='+')
args = parser.parse_args()

if args.states == None or len(args.states) <= 1:
  raise ValueError('Should specify at least 2 states')

# reading the automaton
(alphabet, outputs, all_states, delta, labda) = read_machine(args.filename)
states = args.states
length = args.length

measure_time('Constructed automaton with', len(all_states), 'states and', len(alphabet), 'symbols')


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

# In order to print the "unsat core", we introduce enablind
# variables evar(s). This simply means: the state s participates
# in the ADS construction. The unsat core will tell us which
# subset of states already has no ADS.
def evar(s):
  return var(('enable', s))

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


# For each state s, we construct a path of possible successor states,
# following the guessed words. This path should be consistent with delta,
# and we also record the outputs along this path. The outputs are later
# used to decide whether we found a different output.
possible_outputs = {}
possible_states = {}
for s in tqdm(states, desc="CNF paths"):
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
for s in tqdm(states, desc="CNF diffs"):
  for t in states:
    # We skip s == t, since those state are equivalent.
    # I am not sure whether we can skip s <= t, since our construction
    # below is not symmetrical. We do however include a clause which
    # states that the dvars are symmetrical. This should help the
    # solver a little bit.
    if s == t:
      continue

    enable_for_core = [-evar(s), -evar(t)]

    # First, we require that there is a difference on the paths of s and t
    # Unless the states s and t are not enabled.
    solver.add_clause(enable_for_core + [dvar(s, t, i) for i in range(length)])

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
          solver.add_clause(enable_for_core + [-avar(s, i, a), avar(t, i, a)])
        else:
          # We do one direction -d2var(s, t, i-1) /\ avar(s, i, a) => avar(t, i, a)
          solver.add_clause(enable_for_core + [d2var(s, t, i-1), -avar(s, i, a), avar(t, i, a)])

      # Also, if there is no difference yet, the successor states must
      # be different. (If they collapse, no difference can ever occur.)
      # This is not strictly necessary as a clause, but it makes the
      # solving much faster.
      # -d2var(s, t, i-1) /\ svar(s, i, s2) => -svar(t, i, s2)
      if i > 0:
        for s2 in possible_states[(s, i)]:
          if s2 in possible_states[(t, i)]:
            solver.add_clause(enable_for_core + [d2var(s, t, i-1), -svar(s, i, s2), -svar(t, i, s2)])

      # We encode: if there is a difference, then the outputs should
      # actually differ. (We do not have to encode the other implication!)
      # x_('d', s, t, i) /\ x_('o', s, i, o) => -x_('o', t, i, o)
      # Note: when o is not possible for state t, then the clause already holds
      outputs_s = possible_outputs[(s, i)]
      outputs_t = possible_outputs[(t, i)]
      for o in outputs_s:
        if o in outputs_t:
          solver.add_clause(enable_for_core + [-dvar(s, t, i), -ovar(s, i, o), -ovar(t, i, o)])


measure_time('Constructed CNF with', solver.nof_clauses(), 'clauses and', solver.nof_vars(), 'variables')


# ******************
# Solving and output
# ******************

# We set up some things for nice output
console = Console(markup=False, highlight=False)
max_state_length = max([len(str) for str in states])

# Solve it!
current_states = states
solution = False

while current_states and not solution:
  enabled_states = [evar(s) for s in current_states]
  solution = solver.solve(assumptions=enabled_states)
  measure_time('Solver finished')

  # If there is no solution, we can exit. As far as I know
  # there is no relevant information in the "core", as there
  # are no assumptions used in our encoding.
  if solution:
    console.print('! ADS of length', length, 'for', len(current_states), 'states exists', style='bold green')
    measure_total_time('Done')
    exit()

  console.print('! no ADS of length', length, 'for', len(current_states), 'states', style='bold red')

  core = solver.get_core()
  core_set = set()
  for l in core:
    if l > 0:
      core_set.add(l)

  core_states = [s for s in states if evar(s) in core_set]
  fine_states = [s for s in states if evar(s) not in core_set]
  print(len(core_states), 'states in the unsat core')
  print('core states =', core_states)
  print('fine states =', fine_states)

  current_states = fine_states


measure_total_time('Done')
