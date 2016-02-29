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
    accessConstraintEncoding = encodeAccessConstraint(accessConstraint, conf.entryResource)
    return Implies(targetEncoding, accessConstraintEncoding)      

def encodeAccessConstraint(accessConstraint, resource):
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
        constraint = encodeAccessConstraint(accessConstraint[1], resource)
        return Not(constraint)
    ###
    ### BINARY: =>, AND, OR
    ###    
    elif any(accessConstraint[0] == x for x in ['and', 'or', '=>']):
        constraintLeft = encodeAccessConstraint(accessConstraint[1], resource)
        constraintRight = encodeAccessConstraint(accessConstraint[2], resource)
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
            constraint = encodeAccessConstraint(accessConstraint, successor)
            successorConstraints.append(And(template.PEPTemplate(PEP), constraint))
        return Or(successorConstraints)
    ###
    ### AX
    ###
    elif accessConstraint[0] == 'AX':
        successorConstraints = []
        for PEP in networkx.edges_iter(conf.resourceStructure, resource):
            successor = PEP[1]
            constraint = encodeAccessConstraint(accessConstraint, successor)
            successorConstraints.append(Implies(template.PEPTemplate(PEP), constraint))
        return And(successorConstraints)
    ###
    ### EU
    ###
    elif accessConstraint[0] == 'EU':
        return encodeUntilAccessConstraint(accessConstraint, resource, set())        
    ###
    ### AU
    ###
    elif accessConstraint[0] == 'AU':
        return encodeUntilAccessConstraint(accessConstraint, resource, set())
    ###
    ### SYNTACTIC SHORTHANDS
    ###
    elif accessConstraint[0] == 'AR':
        return encodeAccessConstraint(['not', ['EU', ['not', accessConstraint[1]], ['not', accessConstraint[2]]]], resource)
    elif accessConstraint[0] == 'AG':
        return encodeAccessConstraint(['not', ['EU', 'true', ['not', accessConstraint[1]]]], resource)
    elif accessConstraint[0] == 'EF':                            
        return encodeAccessConstraint(['EU', 'true', accessConstraint[1]], resource)
    elif accessConstraint[0] == 'AF':
        return encodeAccessConstraint(['AU', 'true', accessConstraint[1]], resource)
    else:
        raise NameError('Could not encodeAccessConstraint access constraint: ' + str(accessConstraint))


def encodeUntilAccessConstraint(accessConstraint, resource, visited):
    print 'encodeUntilAccessConstraint', resource, visited
    if accessConstraint[0] == 'EU':
        accessConstraint1 = accessConstraint[1]
        accessConstraint2 = accessConstraint[2]
        
        accessConstraint1Encoded = encodeAccessConstraint(accessConstraint1, resource)
        accessConstraint2Encoded = encodeAccessConstraint(accessConstraint2, resource)                
        
        successorConstraints = []
        for PEP in networkx.edges_iter(conf.resourceStructure, resource):
            successor = PEP[1]            
            if successor in visited:
                continue
            succVisited = set(visited)
            succVisited.add(resource)
            successorAccessConstraintEncoded = encodeUntilAccessConstraint(accessConstraint, successor, succVisited)
            pepTemplate = template.PEPTemplate(PEP)
            successorConstraints.append(And(pepTemplate, successorAccessConstraintEncoded))
        return Or(accessConstraint2Encoded, And(accessConstraint1Encoded, Or(successorConstraints)))        
            
    elif accessConstraint[0] == 'AU':
        accessConstraint1 = accessConstraint[1]
        accessConstraint2 = accessConstraint[2]
        
        accessConstraint1Encoded = encodeAccessConstraint(accessConstraint1, resource)
        accessConstraint2Encoded = encodeAccessConstraint(accessConstraint2, resource)
                        
        successorConstraints = []
        noBackEdgesConstraints = []
        existsSuccessorConstraints = []
        
        for PEP in networkx.edges_iter(conf.resourceStructure, resource):
            successor = PEP[1]            
            if successor in visited:
                noBackEdgesConstraints.append(Not(template.PEPTemplate(PEP)))
                continue
            
            existsSuccessorConstraints.append(template.PEPTemplate(PEP))
                                    
            succVisited = set(visited)
            succVisited.add(resource)
            successorAccessConstraintEncoded = encodeUntilAccessConstraint(accessConstraint, successor, succVisited)
            pepTemplate = template.PEPTemplate(PEP)
            successorConstraints.append(Implies(pepTemplate, successorAccessConstraintEncoded))
            
        noBackEdges = And(noBackEdgesConstraints)
        existsSuccessor = Or(existsSuccessorConstraints)
            
        return Or(accessConstraint2Encoded, And(accessConstraint1Encoded, noBackEdges, existsSuccessor, And(successorConstraints)))
    else:
        raise NameError('Not an until access constraint:', accessConstraint)