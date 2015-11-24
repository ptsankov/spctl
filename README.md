# Folder structure

1. /case-studies
  - the three case studies
2. /polisy
  - the python implementation of the policy synthesizer
3. /running-example
  - the running example

# Running the policy synthesizer

```
python synth.py <synthesis configuration file>
```

# Synthesis configuration files

A synthesis configuration file encodes a synthesis problem.

## Example synthesis configuration file

```
[SYNTHESIS]
STRUCTURE=structure.adj
REQUIREMENTS=requirements.ctl
SUBJECT_ATTRIBUTES=subject.attrs
RESOURCE_ATTRIBUTES=resource.attrs
FIXED_GRAMMAR=true
OUTPUT=output.log

[GRAMMAR]
NUMBER_OF_ENUMERATED=2
NUMBER_OF_NUMERIC=1
NUMBER_OF_DISJUNCTIONS=2
```

# Software dependencies

1. Python interpreter
2. Z3 SMT solver with python packages (Z3Py)

# How to use


