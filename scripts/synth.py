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
import policy_synth
from networkx.classes.function import set_node_attributes

def solve_synthesis_instance(reqsStr, num_ors, num_enum, num_numeric):
    policy_synth.setTemplateSize(num_ors, num_enum, num_numeric)            
    reqs = []
    for reqStr in reqsStr:
        if not reqStr.startswith('('):
            print reqStr
        else:
            reqs.append(ctl_grammar.parseRequirement(reqStr))    
    return policy_synth.synth(graph, reqs, attrs)

if __name__ == '__main__':
    
    if len(sys.argv) not in [5, 8]:
        print 'Usage: {} <graph file> <attributes file> <resources file> <requirements> [<num ors> <# enums> <# numeric>]'.format(sys.argv[0])
        sys.exit(-1)
    graphFilename = sys.argv[1]
    attributesFilename = sys.argv[2]
    resourcesFilename = sys.argv[3]
    reqsFilename = sys.argv[4]

    print 'Resource graph filename:', graphFilename
    print 'Attributes filename:', attributesFilename
    print 'Resources  filename:', resourcesFilename
    print 'Requirements filename:', reqsFilename

    for filename in [graphFilename, attributesFilename, resourcesFilename, reqsFilename]:
        if not os.path.isfile(filename):
            print filename, 'is not a file'
            sys.exit(-1)            

    graph = nx.read_adjlist(graphFilename, create_using = nx.DiGraph())    
    print 'Resources in the resource graph:', graph.nodes()    
        
    with open(attributesFilename) as f:
        attrs = f.readlines()
    attrs = [a.strip() for a in attrs]
    print 'Attributes:', attrs
    setAttrVars(attrs)

    with open(resourcesFilename) as f:
        resAttrsStr = f.readlines()
    resAttrsStr = [x.strip() for x in resAttrsStr]    
        
    for resAttrs in resAttrsStr:
        resAttrMap = {}
        attrName = resAttrs.split('|')[0]
        attrPairs = resAttrs.split('|')[1]
        for attrPair in attrPairs.split(','):
            resId = attrPair.split(':')[0]
            attrVal = attrPair.split(':')[1]            
            resAttrMap[resId] = attrVal
        set_node_attributes(graph, attrName, resAttrMap)
    resAttrMap = {}
    for n in graph.nodes():
        resAttrMap[n] = n
    set_node_attributes(graph, 'room_id', resAttrMap)

    with open(reqsFilename) as f:
        reqsStr = [x.strip() for x in f.readlines()]

    if len(sys.argv) == 5:
        policy = unsat
        num_ors = 1
        num_enum = 0
        num_numeric = 0
        while policy == unsat:
            min_size = min(num_ors, num_enum, num_numeric)
            inc = False
            if num_ors == min_size:
                num_ors += 1
                inc = True
            if not inc and num_enum == min_size:
                num_enum += 1
                inc = True
            if not inc and num_numeric == min_size:
                num_numeric += 1
            print 'Template size', num_ors, num_enum, num_numeric
            policy = solve_synthesis_instance(reqsStr, num_ors, num_enum, num_numeric)        
    else:
        policy = solve_synthesis_instance(reqsStr, int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7]))
                                       
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