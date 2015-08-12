'''
Created on Aug 11, 2015

@author: ptsankov
'''
from utils.helperMethods import setOutputFile, close, INIT_RESOURCE
from z3 import parse_smt2_file, Solver, CheckSatResult
from utils.smt2Translation import declareRooms, declarePolicyTemplates,\
    declareCTLMustHold, modelToPolicy, modelToSimplifiedPolicy
from ctl.ctl_to_sat import ctlToSAT
from z3consts import Z3_L_FALSE
import sys

outputFilename = 'output.smt2'

def policyGuidedSynth(graph, attrs, reqs):
    print 'Running the policy-guided synthesis algorithm'
    outFile = open(outputFilename, 'w')
    setOutputFile(outFile)
    
    declareRooms(graph)    
    declarePolicyTemplates(graph, attrs) 
                 
    ctlFuncNames = []
    for req in reqs:
        print 'Processing requirement:', req
        ctlFuncName = ctlToSAT(req, graph, attrs, INIT_RESOURCE)
        ctlFuncNames.append(ctlFuncName)
        
    declareCTLMustHold(ctlFuncNames, attrs)

    s = Solver()
    close()
    f = parse_smt2_file(outputFilename)
    s.add(f)
    if s.check() == CheckSatResult(Z3_L_FALSE):
        print 'Cannot find a model'
        sys.exit(-1)
    model = s.model()
    modelToPolicy(model, graph, attrs)
    print 'simpler'
    modelToSimplifiedPolicy(model, graph, attrs)