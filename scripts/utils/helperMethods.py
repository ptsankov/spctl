from z3 import Bool, Not, And, Or, Implies

OUTPUT_FILE = None
DEBUG = True
INIT_RESOURCE = 'Outside'
ATTR_VARS = {}
EDGE_VARS = {}

def setOutputFile(outFile):
    global OUTPUT_FILE
    OUTPUT_FILE = outFile

def write(s):
    assert OUTPUT_FILE is not None
    if DEBUG:
        print s
    OUTPUT_FILE.write(s)
    
def close():
    OUTPUT_FILE.close()
    
    
def setAttrVars(attrs):
    for attr in attrs:
        ATTR_VARS[attr] = Bool(attr)

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
