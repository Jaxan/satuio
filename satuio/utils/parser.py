"""
Function to read a Mealy machine in .dot format (as outputted by
LearnLib). This is not a battle-tested parser, but a quick and
dirty parser. Good enough for now. All states, inputs and output
are stored as strings.

© Joshua Moerman, Open Universiteit, 2022
"""

def read_machine(filename):
  alphabet = set()
  outputs = set()
  states = set()

  delta = {}
  labda = {}

  with open(filename) as file:
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

  return (alphabet, outputs, states, delta, labda)
