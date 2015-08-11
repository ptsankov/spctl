'''
Created on Aug 11, 2015

@author: ptsankov
'''
from z3 import Solver, Bool, Not, And, Implies, Or, sat, simplify
from ctl.ctl_grammar import CTLGrammar
from ctl import ctl_grammar

ATTR_VARS = {}

def strToZ3(propFormula):
    if propFormula[0] == 'not':
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
        nextReqs = []
        depReqs = []
        for curReq in curReqs:
            s.reset()
            s.add(And(strToZ3(curReq[0]), strToZ3(req[0])))
            if s.check() == sat:
                # the two requirements overlap
                depReqs.append(curReq)
            else:
                # the requirements are independent
                nextReqs.append(curReq)
                
        for depReq in depReqs:
            # Case (Q and Qi, F and Fi)
            depProp = strToZ3(depReq[0])
            reqProp =  strToZ3(req[0])
            newReqProp = ctl_grammar.parsePropositionalFormula(simplify(And(depProp, reqProp)).sexpr())
            newReqCTL = ['and', depReq[1], req[1]]
            newReq = [newReqProp, newReqCTL]
            nextReqs.append(newReq)
            
            # Case (not Q and Qi, not F and Fi)
            newReqProp = ctl_grammar.parsePropositionalFormula(simplify(And(depProp, Not(reqProp))).sexpr())
            newReqCTL = depReq[1]
            newReq = [newReqProp, newReqCTL]
            nextReqs.append(newReq)
        
        # Case (Q and not Q1 and ... and not Qn, F and not F1 and ... not Fn)
        tmp = simplify(And([Not(strToZ3(depReq[0])) for depReq in depReqs]))
        reqProp =  strToZ3(req[0])
        newReqProp = ctl_grammar.parsePropositionalFormula(simplify(And(reqProp, tmp)).sexpr())                
        newReqCTL = req[1]
        newReq = [newReqProp, newReqCTL]
        nextReqs.append(newReq)    
        
        curReqs = nextReqs
        
    return curReqs

def decomposeSynth(graph, attrs, reqs):
    print 'Running the decompose synthesis algorithm'    
        
    for attr in attrs:
        ATTR_VARS[attr] = Bool(attr)
        
    decomposedReqs = decomposeReqs(reqs)
    for r in decomposedReqs:
        if r[0] != 'false':
            print r
            print '========================'