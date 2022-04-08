"""
Functions to measure time and print stuff nicely, etc

© Joshua Moerman, Open Universiteit, 2022
"""

from time import time

# *******************************
# Functions for some time logging
# *******************************

start = time()
start_total = start

def time_since_start():
  return time() - start_total

def now():
  t = time_since_start()
  return f"[yellow]{t:6.2f}[/yellow]"


# ****************************
# Functions related to solving
# ****************************

# This stores all true variables in a set, for easy lookup
def get_truth(solver):
  m = solver.get_model()
  truth = set()
  for l in m:
    if l > 0:
      truth.add(l)
  return truth


# *****************
# General functions
# *****************

# Get some element from a set, doesn't matter which.
# (I could not find this in the standard library.)
def some_elem(collection):
  for x in collection:
    return x
