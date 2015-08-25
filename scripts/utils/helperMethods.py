from z3 import Bool, Not, And, Or, Implies, Int

INIT_RESOURCE = 'out'
ATTR_BOOL_VARS = {}
ATTR_NUMERIC_VARS = {}
EDGE_VARS = {}

def setAttrVars(attrs):
    for attr in attrs:
        name = attr.split(':')[0].strip()
        type = attr.split(':')[1].strip()
        if type == 'boolean':
            ATTR_BOOL_VARS[attr] = Bool(attr)
        elif type == 'numeric':
            ATTR_NUMERIC_VARS[attr] = Int(attr)

def setEdgeVars(graph):
    # declare variables for all edges
    for e in graph.edges():
        EDGE_VARS[e] = Bool(e[0] + '_' + e[1])

def strToZ3(propFormula):
    if propFormula in ATTR_VARS.keys():
        return ATTR_VARS[propFormula]
    elif propFormula[0] == 'not':
        return Not(strToZ3(propFormula[1]))
    elif propFormula[0] == 'and':
        return And([strToZ3(x) for x in propFormula[1:]])
    elif propFormula[0] == 'or':
        return Or([strToZ3(x) for x in propFormula[1:]])
    elif propFormula[0] == '=>':
        return Implies(strToZ3(propFormula[1]), strToZ3(propFormula[2]))
    elif propFormula == 'true':
        return True
    elif propFormula == 'false':
        return False
    else:
        raise NameError('could not convert propositional formula to the Z3 format')

def Z3toStr(z3Formula):
    if z3Formula.decl().name() in ATTR_VARS.keys():
        return z3Formula.decl().name()
    elif z3Formula.decl().name() == 'not':
        return ['not', Z3toStr(z3Formula.arg(0))]
    elif z3Formula.decl().name() == 'and':
        return ['and'] + [Z3toStr(child) for child in z3Formula.children()]
    elif z3Formula.decl().name() == 'or':
        return ['or'] + [Z3toStr(child) for child in z3Formula.children()]
    elif z3Formula.decl().name() == '=>':
        return ['=>'] + [Z3toStr(child) for child in z3Formula.children()]
    elif z3Formula == True:
        return ['true']
    elif z3Formula == False:
        return ['false']
    else:
        raise NameError('could not convert Z3 formula to string')