'''
Created on Aug 11, 2015

@author: ptsankov
'''
from z3 import Solver, Bool, Not, And, Implies, Or
from ctl import ctl_grammar

ATTR_VARS = {}

def z3Prop(propFormula):
    if propFormula[0] == '!':
        return Not(z3Prop(propFormula[1]))
    elif propFormula[0] == '&':
        return And(z3Prop(propFormula[1]), z3Prop(propFormula[2]))
    elif propFormula[0] == '|':
        return Or(z3Prop(propFormula[1]), z3Prop(propFormula[2]))
    elif propFormula[0] == '->':
        return Implies(z3Prop(propFormula[1]), z3Prop(propFormula[2]))
    elif propFormula == 'true':
        return True
    elif propFormula == 'false':
        return False
    else:
        # must be an attribute
        assert propFormula in ATTR_VARS.keys()
        return ATTR_VARS[propFormula]

def decomposeSynth(graph, attrs, reqs):
    print 'Running the decompose synthesis algorithm'    
    
    s = Solver()
    
    for attr in attrs:
        ATTR_VARS[attr] = Bool(attr)
        
    # decouple requirements into
    # (Q1, F1), ..., (Qn, Fn) such that for all i, j we have (Qi and Qj = False)
    
    decomposedReqs = []
    
    for req in reqs:
        propFormula = req[0]
        ctlFormula = req[1]
        print z3Prop(propFormula)
        
    