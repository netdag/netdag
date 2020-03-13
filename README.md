# NetDAG

We are committed to making our scheduler implementation publicly
available. If our paper is accepted, we will improve reusability of our
code, i.e. as a tool release, and provide more sample inputs. For now,
we include four files. `netdag.py` includes our scheduler
implementation, `network_statistics.py` is a configuration file where we
can write down various soft/weakly-hard lambda functions,
`simple-task-graph.xml.gz` is a simple test input, and
`simulator.py` includes our validation tools.

## Dependencies

Our code is implemented in Python3 (vers. 3.6.9) and has the following python
dependencies:

 - pysmt: for SMT formula manipulation
 - numpy
 - graph_tool: for reading the input file and task-dependency graph manipulation
 - cvxpy: for MILP formula manipulation
 - drawSVG: for drawing obtained schedules
 - colour: for color manipulation

and the following non-python dependencies:

 - z3, yices as SMT backends for pysmt (installed via pysmt-install)
 - GUROBI as MILP backend for cvxpy

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
