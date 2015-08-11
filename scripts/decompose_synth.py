'''
Created on Aug 11, 2015

@author: ptsankov
'''
from z3 import Solver, Bool, Not, And, Implies, Or, sat, simplify

ATTR_VARS = {}

def strToZ3(propFormula):
    if propFormula[0] == '!':
        return Not(strToZ3(propFormula[1]))
    elif propFormula[0] == '&':
        return And(strToZ3(propFormula[1]), strToZ3(propFormula[2]))
    elif propFormula[0] == '|':
        return Or(strToZ3(propFormula[1]), strToZ3(propFormula[2]))
    elif propFormula[0] == '->':
        return Implies(strToZ3(propFormula[1]), strToZ3(propFormula[2]))
    elif propFormula == 'true':
        return True
    elif propFormula == 'false':
        return False
    else:
        # must be an attribute
        assert propFormula in ATTR_VARS.keys()
        return ATTR_VARS[propFormula]
    
# decouple requirements into
# (Q1, F1), ..., (Qn, Fn) such that for all i, j we have (Qi and Qj = False)
def decomposeReqs(reqs):
    curReqs = []
    curReqs.append(reqs.pop())
    
    s = Solver()
    
    for req in reqs:        
        print 'Requirement', req
        print 'Current requirements', curReqs
        nextReqs = []
        depReqs = []
        for curReq in curReqs:
            print 'Current requirement', curReq
            s.reset()
            s.add(And(strToZ3(curReq[0]), strToZ3(req[0])))
            if s.check() == sat:
                print 'dependent requirement'
                # the two requirements overlap
                depReqs.append(curReq)
            else:
                # the requirements are independent
                print 'already independent'
                nextReqs.append(curReq)
                
        for depReq in depReqs:
            depProp = strToZ3(depReq[0])
            reqProp =  strToZ3(req[0])
            newReqProp = simplify(And(depProp, reqProp)).sexpr()
            newReqCTL = '(and ' + depReq[1] + ' ' + req[1] + ')'
            newReq = '(' + newReqProp + ', ' +  newReqCTL + ')'
            nextReqs.append(newReq)
                
        print 'Requirement', req        
        propFormula = req[0]
        print 'Propositional formula', propFormula
        ctlFormula = req[1]
        print 'CTL formula', ctlFormula
        print strToZ3(propFormula)
        
        depReqs = nextReqs
        
    return curReqs

def decomposeSynth(graph, attrs, reqs):
    print 'Running the decompose synthesis algorithm'    
        
    for attr in attrs:
        ATTR_VARS[attr] = Bool(attr)
        
    decomposedReqs = decomposeReqs(reqs)
    for r in decomposedReqs:
        print r