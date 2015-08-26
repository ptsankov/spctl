from z3 import Bool, Not, And, Or, Implies, Int, EnumSort, Const

INIT_RESOURCE = 'out'
BOOL_VARS = {}
ENUM_VARS = {}
ENUM_VALUES = {}
NUMERIC_VARS = {}
EDGE_VARS = {}

def setAttrVars(attrs):
    for attr in attrs:
        attrName = attr.split(':')[0].strip()
        attrType = attr.split(':')[1].strip()
        if attrType == 'bool':
            BOOL_VARS[attrName] = Bool(attrName)
        elif attrType == 'enum':
            values = attr.split(':')[2].strip().split(',')
            newEnumSort = EnumSort(attrName, values)
            ENUM_VARS[attrName] = Const(attrName, newEnumSort[0])
            ENUM_VALUES[attrName] = {}
            for enumVal in newEnumSort[1]:
                ENUM_VALUES[attrName][str(enumVal)] = enumVal                
        elif attrType == 'numeric':
            print 'numeric type', attrName
            NUMERIC_VARS[attrName] = Int(attrName)
        else:
            raise NameError('unknown attribute type: '+ attrType)
        
def setEdgeVars(graph):
    # declare variables for all edges
    for e in graph.edges():
        EDGE_VARS[e] = Bool(e[0] + '_' + e[1])


def strToZ3(policy):
    if policy in BOOL_VARS.keys():
        return BOOL_VARS[policy]
    elif policy[0] in ENUM_VARS.keys():
        var = ENUM_VARS[policy[0]] 
        disjunctions = []
        for val in policy[2]:
            disjunctions.append(Or(ENUM_VARS[str(var)] == ENUM_VALUES[str(var)][val]))
        return Or(disjunctions)
    elif policy[0] in NUMERIC_VARS.keys():
        var = NUMERIC_VARS[policy[0]]
        _min = int(policy[2][0])
        _max = int(policy[2][1] )       
        return And(var >= _min, var <= _max)
    elif policy[0] == 'not':
        return Not(strToZ3(policy[1]))
    elif policy[0] == 'and':
        return And([strToZ3(x) for x in policy[1:]])
    elif policy[0] == 'or':
        return Or([strToZ3(x) for x in policy[1:]])
    elif policy[0] == '=>':
        return Implies(strToZ3(policy[1]), strToZ3(policy[2]))
    elif policy == 'true':
        return True
    elif policy == 'false':
        return False
    else:
        raise NameError('could not convert propositional formula to the Z3 format')

def Z3toStr(z3Formula):
    raise NameError('fix the Z3toStr method')
    if z3Formula.decl().name() in BOOL_VARS.keys():
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