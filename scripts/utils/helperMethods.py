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
        
    print BOOL_VARS
    print ENUM_VARS
    print ENUM_VALUES
    print NUMERIC_VARS

def setEdgeVars(graph):
    # declare variables for all edges
    for e in graph.edges():
        EDGE_VARS[e] = Bool(e[0] + '_' + e[1])


def strToZ3(propFormula):
    if propFormula in BOOL_VARS.keys():
        return BOOL_VARS[propFormula]
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