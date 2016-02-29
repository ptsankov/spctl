'''
Created on Aug 12, 2015

@author: ptsankov
'''
from z3 import Solver, Not, And, Or, Implies, sat, unsat, ForAll
import time
import conf
import template
from utils.helperMethods import log
import networkx

def solve():        
    start = time.time()
    s = Solver()
    for req in conf.reqs:
        print req
        log('Translating requirement: ' + str(req))
        target = req[0]
        accessConstraint = req[1]
             
        requirementEncoding = encodeRequirement(target, accessConstraint)  
        s.add(ForAll(template.getAttributeVars(), requirementEncoding))         

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

def encodeRequirement(target, accessConstraint):
    targetEncoding = template.encodeTarget(target)
    accessConstraintEncoding = encode(accessConstraint, conf.entryResource)
    return Implies(targetEncoding, accessConstraintEncoding)      


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
        successorConstraints = []
        for PEP in networkx.edges_iter(conf.resourceStructure, resource):
            successor = PEP[1]
            constraint = encode(accessConstraint, successor)
            successorConstraints.append(And(template.PEPTemplate(PEP), constraint))
        return Or(successorConstraints)
    ###
    ### AX
    ###
    elif accessConstraint[0] == 'AX':
        successorConstraints = []
        for PEP in networkx.edges_iter(conf.resourceStructure, resource):
            successor = PEP[1]
            constraint = encode(accessConstraint, successor)
            successorConstraints.append(Implies(template.PEPTemplate(PEP), constraint))
        return And(successorConstraints)
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
