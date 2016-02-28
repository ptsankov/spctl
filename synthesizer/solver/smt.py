'''
Created on Aug 12, 2015

@author: ptsankov
'''
from z3 import Solver, Not, And, Or, Implies, sat, unsat, ForAll
import networkx as nx
import time
import conf
import template
from utils.helperMethods import log

def solve():        
    start = time.time()
    s = Solver()
    for req in conf.reqs:
        print req
        log('Translating requirement: ' + str(req))
        reqProp = req[0]
               
        constraint = encode(req[1], conf.entryResource)      
        s.add(ForAll([BOOL_VARS[varName] for varName in BOOL_VARS.keys()] + [ENUM_VARS[varName] for varName in ENUM_VARS.keys()] + [NUM_VAR], Implies(And([strToZ3(reqProp), NUM_VAR >= 0, NUM_VAR <= 24]), constraint)))

    timeToTranslate = time.time() - start    
    log('DATA| Translation time: ' + str(timeToTranslate))
        
    
    log('SMT Solving')
    
    start = time.time()
    if s.check() == sat:
        policy = {}        
        model = s.model()        
        timeToSolve = time.time() - start
        log('DATA| SMT time: ' + str(timeToSolve))
        for PEP in conf.PEPS:           
            policy[PEP] = template.PEPPolicy(PEP, model) 
        return policy
    else:    
        return unsat


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


def isConstraint(formula):
    if formula[0] == 'not':
        return isConstraint(formula[1])
    elif formula[0] == 'and':
        return isConstraint(formula[1]) and isConstraint(formula[2])
    elif formula[0] == '=>':
        return (not isConstraint(formula[1])) and isConstraint(formula[2])
    elif formula[0] == 'or':
        return (isConstraint(formula[1])) or isConstraint(formula[2])
    else:
        if len(formula) == 3 and formula[1] == 'in':
            return True
        return False

def evalResourceConstraint(graph, resource, constraint):
    if constraint[0] == 'not':
        return not evalResourceConstraint(graph, resource, constraint[1])
    elif constraint[0] == 'and':
        return evalResourceConstraint(graph, resource, constraint[1]) and evalResourceConstraint(graph, resource, constraint[2])
    elif constraint[0] == '=>':
        return (not evalResourceConstraint(graph, resource, constraint[1])) and evalResourceConstraint(graph, resource, constraint[2])
    elif constraint[0] == 'or':
        return evalResourceConstraint(graph, resource, constraint[1]) or evalResourceConstraint(graph, resource, constraint[2])
    else:
        assert isConstraint(constraint)
        attrName = constraint[0]
        attrVals = constraint[2]
        attrVal = graph.node[resource][attrName]
        return any(attrVal == x for x in attrVals)        

def encode(accessConstraint, resource):
    ###
    ### TRUE/FALSE
    ### 
    if accessConstraint == 'true':
        return True
    elif accessConstraint == 'false':
        return False
    ###
    ### ATTRIBUTE CONSTRAINT
    ###
    elif len(accessConstraint) == 3 and accessConstraint[1] == 'in':
        attrName = accessConstraint[0]
        attrVals = accessConstraint[2]
        attrVal = conf.resourceStructure.node[resource][attrName]
        return any(attrVal == x for x in attrVals)
    ###
    ### UNARY: NOT
    ###
    elif accessConstraint[0] == 'not':
        constraint = encode(accessConstraint[1], resource)
        return Not(constraint)
    ###
    ### BINARY: =>, AND, OR
    ###    
    elif any(accessConstraint[0] == x for x in ['and', 'or', '=>']):
        constraintLeft = encode(accessConstraint[1], resource)
        constraintRight = encode(accessConstraint[2], resource)
        if accessConstraint[0] == 'and':
            return And(constraintLeft, constraintRight)
        elif accessConstraint[0] == 'or':
            return Or(constraintLeft, constraintRight)
        elif accessConstraint[0] == '=>':
            return Implies(constraintLeft, constraintRight)
    ###
    ### EX
    ###
    elif accessConstraint[0] == 'EX':
        raise NameError('todo')
    ###
    ### AX
    ###
    elif accessConstraint[0] == 'AX':
        raise NameError('todo')
    ###
    ### EU
    ###
    elif accessConstraint[0] == 'EU':
        raise NameError('todo')
    ###
    ### AU
    ###
    elif accessConstraint[0] == 'AU':
        raise NameError('todo')
    ###
    ### SYNTACTIC SHORTHANDS
    ###
    elif accessConstraint[0] == 'AR':
        return encode(['not', ['EU', ['not', accessConstraint[1]], ['not', accessConstraint[2]]]], resource)
    elif accessConstraint[0] == 'AG':
        return encode(['not', ['EU', 'true', ['not', accessConstraint[1]]]], resource)
    elif accessConstraint[0] == 'EF':                            
        return encode(['EU', 'true', accessConstraint[1]], resource)
    elif accessConstraint[0] == 'AF':
        return encode(['AU', 'true', accessConstraint[1]], resource)
    else:
        raise NameError('Could not encode access constraint: ' + str(accessConstraint))
