satuio
======

Using SAT solvers to construct UIOs and ADSs for Mealy machines.


## Dependencies

This project uses Python3. It uses the following packages which can be
installed with `pip`.

* [`pysat`](https://github.com/pysathq/pysat)
* [`tqdm`](https://github.com/tqdm/tqdm)
* [`rich`](https://github.com/Textualize/rich/)


## Usage

All scripts show their usage with the `--help` flag. Note that the
flags and options are subject to change, since this is WIP.

```bash
# Finding UIO sequences of fixed length in a Mealy machine
python3 satuio/uio.py --help

# Finding UIO sequences while incrementing the length in a Mealy machine
python3 satuio/uio-incr.py --help

# Finding an ADS in a Mealy machine for a set of states
python3 satuio/ads.py --help
```

The solver can be specified (as long as pysat supports it). The default is
[Glucose3](https://www.labri.fr/perso/lsimon/glucose/), as that worked
well on the examples.


## Copyright

© Joshua Moerman, Open Universiteit, 2022
