# Import the solvers and utilities
from pysat.solvers import Solver
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
import time                         # Time for rough timing measurements
import argparse                     # Command line options
from tqdm import tqdm               # Import fancy progress bars
from rich.console import Console    # Import colorized output

solver_name = 'g3'
verbose = True

start = time.time()
def measure_time(*str):
  global start
  now = time.time()
  print('***', *str, "in %.3f seconds" % (now - start))
  start = now


# *********************
# Reading the automaton
# *********************

parser = argparse.ArgumentParser()
parser.add_argument('filename', help='File of the mealy machine (dot format)')
parser.add_argument('length', help="Length of the uio", type=int)
args = parser.parse_args()

length = args.length

alphabet = set()
outputs = set()
states = set()
bases = set(['s0', 's4', 's37', 's555'])

delta = {}
labda = {}

# Quick and dirty .dot parser
with open(args.filename) as file:
  for line in file.readlines():
    asdf = line.split()
    if len(asdf) > 3 and asdf[1] == '->':
      s = asdf[0]
      t = asdf[2]
      rest = ''.join(asdf[3:])
      label = rest.split('"')[1]
      [i, o] = label.split('/')

      states.add(s)
      states.add(t)
      alphabet.add(i)
      outputs.add(o)

      delta[(s, i)] = t
      labda[(s, i)] = o

measure_time('Constructed automaton with', len(states), 'states and', len(alphabet), 'symbols')


# ********************
# Seting up the solver
# ********************

vpool = IDPool()
solver = Solver(name=solver_name)

# mapping van variabeles: x_... ->  x_i
def var(x):
  return(vpool.id(('uio', x)))

# On place i we have symbol a
def avar(i, a):
  return var(('a', i, a))

# Each state has its own path
# On path s, on place i, there is output o
def ovar(s, i, o):
  return var(('o', s, i, o))

# On path s, we are in state t on place i
def svar(s, i, t):
  return var(('s', s, i, t))

# Extra variable (a la Tseytin transformation)
# On path s, there is a difference on place i
def evar(s, i):
  return var(('e', s, i))

# In order to re-use parts of the formula, we introduce
# enabling variables. These indicate the fixed state for which
# we want to compute an UIO. By changing these variables only, we
# can keep most of the formula the same and incrementally solve it.
# The fixed state is called the "base".
def bvar(s):
  return var(('base', s))

# maakt de constraint dat precies een van de literals waar moet zijn
def unique(lits):
  # deze werken goed: pairwise, seqcounter, bitwise, mtotalizer, kmtotalizer
  # anderen geven groter aantal oplossingen
  # alles behalve pairwise introduceert meer variabelen
  cnf = CardEnc.equals(lits, 1, vpool=vpool, encoding=EncType.seqcounter)
  solver.append_formula(cnf.clauses)

measure_time('Setup solver')


# ********************
# Constructing the CNF
# ********************

# Guessing the word:
# variable x_('in', i, a) says: on place i there is an input a
for i in range(length):
  unique([avar(i, a) for a in alphabet])

# We should only enable one base state (this allows for an optimisation later)
unique([bvar(base) for base in bases])

# For each state s, we construct a path of possible successor states,
# following the guessed word. This path should be consistent with delta,
# and we also record the outputs along this path. The output are later
# used to decide whether we found a different output.
possible_outputs = {}
for s in tqdm(states, desc="CNF construction"):
  # current set of possible states we're in
  current_set = set([s])
  # set of successors for the next iteration of i
  next_set = set()

  for i in range(length):
    # Only one successor state should be enable (probably redundant)
    # For i == 0, this is a single state (namely s)
    unique([svar(s, i, t) for t in current_set])

    # We keep track of the possible outputs
    possible_outputs[(s, i)] = set()

    for t in current_set:
      sv = svar(s, i, t)

      for a in alphabet:
        av = avar(i, a)

        output = labda[(t, a)]
        possible_outputs[(s, i)].add(output)

        # Constraint: when in state t and input a, we output o
        # x_('s', state, i, t) /\ x_('in', i, a) => x_('o', i, labda(t, a))
        # == -x_('s', state, i, t) \/ -x_('in', i, a) \/ x_('o', i, labda(t, a))
        solver.add_clause([-sv, -av, ovar(s, i, output)])

        # when i == length-1 we don't need to consider successors
        if i < length-1:
          next_t = delta[(t, a)]
          next_set.add(next_t)

          # Constraint: when in state t and input a, we go to next_t
          # x_('s', s, i, t) /\ x_('in', i, a) => x_('s', s, i+1, delta(t, a))
          # == -x_('s', s, i, t) \/ -x_('in', i, a) \/ x_('s', s, i+1, delta(t, a))
          solver.add_clause([-sv, -av, svar(s, i+1, next_t)])
    
    # Only one output should be enabled
    # variable x_('out', s, i, a) says: on place i there is an output o of the path s
    unique([ovar(s, i, o) for o in possible_outputs[(s, i)]])

    # Next iteration with successor states
    current_set = next_set
    next_set = set()


# If(f) the output of a state is different than the one from our base state,
# then, we encode that in a new variable. This is only needed when the base
# state is active, so the first literal in these clauses is -bvar(base).
for s in tqdm(states, desc="difference"):
  # Constraint: there is a place, such that there is a difference in output
  # \/_i x_('e', s, i)
  # If s is our base, we don't care
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

      # We encode, if the base is enabled and there is a difference,
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

console = Console(markup=False, highlight=False)
max_state_length = max([len(str) for str in states])

for base in bases:
  console.print('')
  console.print('*** UIO for state', base, style='bold blue')
  b = solver.solve(assumptions=[bvar(base)])
  measure_time('Solver finished')

  if b:
    m = solver.get_model()
    truth = set()
    for l in m:
      if l > 0:
        truth.add(l)
    
    console.print('! UIO of length', length, style='bold green')
    for i in range(length):
      for a in alphabet:
        if avar(i, a) in truth:
          console.print(a, end=' ', style='bold')
    console.print('')

    # For each state, we print the paths and output.
    # We mark the differences red (there can be differences not
    # marked, these are the differences decided in the solving).
    if verbose:
      console.print('! paths')
      for s in states:
        console.print(s.rjust(max_state_length, ' '), '=>', end=' ')
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
              
              console.print(o, end=', ', style=style)
        console.print('')

  else:
    console.print('! no UIO of length', length, style='bold red')
    core = solver.get_core()
    # The core returned by the solver is not interesting:
    # It is only the assumption (i.e. bvar).
