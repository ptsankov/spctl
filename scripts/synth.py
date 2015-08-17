#!/bin/python

'''
Created on May 17, 2015

@author: ptsankov
'''
from z3 import unsat
from utils.helperMethods import setAttrVars
from tabulate import tabulate

import networkx as nx
import sys
import os
from ctl import ctl_grammar
from policy_guided_synth import policyGuidedSynth
from decompose_synth import decomposeSynth
from negative_synth import negativeSynth


if __name__ == '__main__':
    if len(sys.argv) not in [4,5]:
        print 'Usage: {} <graph file> <attributes file> <requirements> [<algorithm>]'.format(sys.argv[0])
        sys.exit(-1)
    graphFilename = sys.argv[1]
    attributesFilename = sys.argv[2]
    reqsFilename = sys.argv[3]
    
    for filename in [graphFilename, attributesFilename, reqsFilename]:
        if not os.path.isfile(filename):
            print filename, 'is not a file'
            sys.exit(-1)
            
    if len(sys.argv) == 5:
        algorithm = sys.argv[4]
        if algorithm not in ['policy-guided', 'decompose', 'negative']:
            print 'Unsupported algorithm. The supported ones are: policy-guided, decompose, negative'
            sys.exit(-1)
            
    print 'Resource graph filename:', graphFilename
    print 'Attributes filename:', attributesFilename
    print 'Requirements filename:', reqsFilename
    
    graph = nx.read_adjlist(graphFilename, create_using = nx.DiGraph())    
    print 'Resources in the resource graph:', graph.nodes()
    
    with open(attributesFilename) as f:
        attrs = f.readlines()
    attrs = [a.strip() for a in attrs]
    print 'Attributes:', attrs
    setAttrVars(attrs)        

    with open(reqsFilename) as f:
        reqsStr = [x.strip() for x in f.readlines()]
        
    reqs = []
    for reqStr in reqsStr:
        if not reqStr.startswith('('):
            print reqStr
        else:
            reqs.append(ctl_grammar.parseRequirement(reqStr))
    
    policy = None
    
    if algorithm == 'decompose':
        policy = decomposeSynth(graph, reqs)
    elif algorithm == 'negative':
        policy = negativeSynth(graph, reqs)
    else:
        policy = policyGuidedSynth(graph, reqs, attrs)
        
    if policy == unsat:
        print 'No solution was found'
        sys.exit(-1)
    
    print '============ SYNTHESIZED POLICY ============'
    policyTable = []
    for edge in graph.edges():
        if edge[0] == edge[1]:
            continue
        check = policy[edge] if type(policy[edge]) == bool else policy[edge].sexpr()
        policyTable.append([edge[0], '->', edge[1], check])
    print tabulate(policyTable, headers = ['FROM', '', 'TO', 'LOCAL POLICY'])