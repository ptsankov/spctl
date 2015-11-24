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

Here `synthesis configuration file` defines a policy synthesis problem. The structure of this file is described below.

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

The section *SYNTHESIS* defines the following attributes:

1. STRUCTURE: A file that defines a resource structure (in adjecency list format)
2. REQUIREMENTS: A file with global requirements expressed in the SpCTL language
3. SUBJECT\_ATTRIBUTES: A file that defines all subject attributes and their domains
4. RESOURCE\_ATTRIBUTES: A fie that defines all resource attributes and their domains
5. FIXED\_GRAMMAR: A boolean flag that indicates whether the synthesizer checks for a solution from a fixed configuration template or not. When the FIXED\_GRAMMAR attribute is set to **FALSE**, the synthesizer begins with the smallest policy configuration template and increases the policy configuration template until a solution is found.

The section *GRAMMAR* defines the configuration tempalte which is used when the FIXED\_GRAMMAR attribute is set to *TRUE*. It defines three attributes:

1. The number of enumerated attributes that the local policies contain
2. The number of numeric attributes that the local policies contain
3. The number of conjunctions

For examples of the above files see our running example.

## Example file that defines a resource structure:

The structure of the running example is as follows:

```
out out lob cor
lob lob out cor
cor cor lob out bur mr
bur bur cor
mr mr cor
```

## Example of a requirements file:

```
((and (role in {visitor}) (time in [8, 20])), (EF (room_id in {mr})))
```

Requirements have the form `(T, AP)` where *T* is a target encoded using the SMT-LIB format and *AP* is an access path. The access path is encoded in a format similar to the standard SMT-lib format, extended with the CTL temporal operators such as (EF AP), (EU AP_1 AP_2), and so forth.

## Example file that defines subject attributes:

```
role:enum:visitor,employee
validPin:bool
time:numeric
```

Here *role* is an enumerated attribute with domain {visitor, employee}, *validPin* is a boolean attribute, and *time* is a numeric attribute.

## Example file that defines resource attributes:

```
zone|room1:public,room2:presecured,room3:presecured,room4:secured
```

Here *zone* is a resource attribute with domain {public, presecured, secured}. There are four resource identifiers room1-4. The labeling of room1, for example, assigns public to the attribute zone.


# Output

The synthesizer outputs the local policy for each edge. The output for our running example is:

```
============ SYNTHESIZED POLICY ============
FROM        TO    LOCAL POLICY
------  --  ----  --------------------------
lob     ->  cor   true
cor     ->  bur   (not (= role visitor)
cor     ->  mr    true
out     ->  lob   true
out     ->  cor   (not (= role visitor))
```

`lob -> cor` defines the policy to be deployed at the main entrance PEP.

The local policies are encoded using the standard SMT-LIB format.