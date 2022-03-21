satuio
======

Using SAT solvers to construct UIOs and ADSs for Mealy machines (aka
finite state machines). Both problems are PSpace-complete, and so a
SAT solver does not really make sense. However, with a given bound
(encoded unary), the problems are in NP, and so can be encoded in SAT.

There are some Mealy machines in `examples` directory. And even for the
machine with roughly 500 states, the encodings are efficient, and
sequences can be found within minutes.


## Dependencies

This project uses Python3. It uses the following packages which can be
installed with `pip` as follows:

```bash
pip3 install python-sat tqdm rich
```

* [`pysat`](https://github.com/pysathq/pysat)
* [`tqdm`](https://github.com/tqdm/tqdm)
* [`rich`](https://github.com/Textualize/rich/)


## Usage

All scripts show their usage with the `--help` flag. Note that the
flags and options are subject to change, since this is WIP. I
recommend to read the source code of these scripts to see what is
going on. (Or read the upcoming paper.)

```bash
# Finding UIO sequences of fixed length in a Mealy machine
python3 satuio/uio.py --help

# Finding UIO sequences while incrementing the length in a Mealy machine
python3 satuio/uio-incr.py --help

# Finding an ADS in a Mealy machine for a set of states
python3 satuio/ads.py --help

# Returning an unsat core in the case an ADS does not exist
python3 satuio/ads-core.py --help
```

The solver can be specified (as long as pysat supports it). The default is
[Glucose3](https://www.labri.fr/perso/lsimon/glucose/), as that worked
well on the examples.


## Copyright

© Joshua Moerman, Open Universiteit, 2022
