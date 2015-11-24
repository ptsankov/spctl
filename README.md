# Folder structure

1. /case-studies
  - the three case studies
2. /polisy
  - the python implementation of the policy synthesizer
3. /running-example
  - the running example

# Software dependencies

1. Python interpreter
2. Z3 SMT solver with python packages (Z3Py)

To check whether Z3Py is properly installed test the following code in your Python interpreter:

```python
>>> from z3 import *
>>> x = Int('x')
>>> solve(x > 1)
[x = 2]
```

# Running the policy synthesizer

The policy synthesizer is executed as follows:

```
python synth.py <synthesis configuration file>
```

Here **synthesis configuration file** defines a policy synthesis problem. The structure of this file is described below.

# Synthesis configuration files

An example synthesis configuration file:

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

The section <b> SYNTHESIS </b> defines the following attributes:
1. STRUCTURE: A file that defines a resource structure (in adjecency list format)
2. REQUIREMENTS: A file with global requirements expressed in the SpCTL language
3. SUBJECT\_ATTRIBUTES: A file that defines all subject attributes and their domains
4. RESOURCE\_ATTRIBUTES: A fie that defines all resource attributes and their domains
5. FIXED\_GRAMMAR: A boolean flag that indicates whether the synthesizer checks for a solution from a fixed configuration template or not. When the FIXED\_GRAMMAR attribute is set to **FALSE**, the synthesizer begins with the smallest policy configuration template and increases the policy configuration template until a solution is found.

For examples of the above files see our running example.

The section <b> GRAMMAR </b> defines the configuration tempalte which is used when the FIXED\_GRAMMAR attribute is set to **TRUE**. It defines three attributes:
1. The number of enumerated attributes that the local policies contain
2. The number of numeric attributes that the local policies contain
3. The number of conjunctions

# Output

The synthesizer outputs the local policy for each edge. The output for our running example is:

============ SYNTHESIZED POLICY ============
FROM        TO    LOCAL POLICY
------  --  ----  --------------------------
lob     ->  cor   true
cor     ->  bur   (not (= role visitor)
cor     ->  mr    true
out     ->  lob   true
out     ->  cor   (not (= role visitor))

lob -> cor defines the policy to be deployed at the main entrance PEP.

The local policies are encoded using the standard SMT-LIB format.