# NetDAG

Scheduler implementation described in our DATE 2020 paper
"Application-Aware Scheduling of Networked Applications over the
Low-Power Wireless Bus."

## Dependencies

Our code is implemented in python (vers. 3.6.9) and has the following python
dependencies:

 - pysmt: for SMT formula manipulation
 - numpy
 - graph_tool: for reading the input file and task-dependency graph manipulation
 - cvxpy: for MILP formula manipulation
 - drawSVG: for drawing obtained schedules
 - colour: for color manipulation

The python dependencies can be installed via

```console
pip install -r requirements.txt
```

Our code has the following non-python dependencies:

 - z3, yices as SMT backends for pysmt
 - graph_tool for graph manipulation and reading/writing input/output files
 - Gurobi Optimizer version 8.0.1 build v8.0.1rc0 (linux64)

z3 and yices can be installed via

```console
pysmt-install --z3 --yices
```

Note that `pysmt-install` comes with the pysmt pip package and will
install the correct versions of z3 and yices for you. Gurobi must be
installed following the instructions on their website, you will need to
first obtain a license (free for academic use). Graph tool can be
installed following the instructions
[here](https://git.skewed.de/count0/graph-tool/-/wikis/installation-instructions).

## Sample usage

To obtain a *soft* real-time schedule:
```python
import netdag
g = netdag.load_graph('simple-task-graph.xml.gz')
network = {'A': 1,
            'B': 1,
            'C': 1,
            'D': 1,
            'GAMMA': 1,
            'LAMBDA': netdag.LAMBDA_SOFT}
model = netdag.get_makespan_optimal_soft_schedule(g, network)
```

to validate the design in simulation:

```python
import simulator
simulator.simulate_soft(g, model, netdag.LAMBDA_SOFT, N_iter=100000)
```

To obtain a *weakly-hard* real-time schedule:
```python
import netdag
g = netdag.load_graph('simple-task-graph.xml.gz')
network = {'A': 1,
            'B': 1,
            'C': 1,
            'D': 1,
            'GAMMA': 1,
            'LAMBDA': netdag.LAMBDA_WEAKLY_HARD}
model = netdag.get_makespan_optimal_weakly_hard_schedule(g, network)
```

and then to validate the design in simulation:
```python
import simulator
simulator.simulate_weakly_hard(g,
            model,
            netdag.LAMBDA_WEAKLY_HARD,
            N_iter=10000,
            K_seq_len=100)
```
