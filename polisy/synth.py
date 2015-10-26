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
from core import requirments_grammar
import algorithms.smt as smt
import ConfigParser
from static import *
from networkx.classes.function import set_node_attributes


def solve_synthesis_instance(reqsStr, numOrs, numEnums, numNumeric):
    smt.setTemplateSize(numOrs, numEnums, numNumeric)            
    reqs = []
    for reqStr in reqsStr:
        if not reqStr.startswith('('):
            print reqStr
        else:
            reqs.append(requirments_grammar.parseRequirement(reqStr))    
    return smt.synth(graph, reqs, attrs)

if __name__ == '__main__':
    global outputFile
    
    if len(sys.argv) != 2:
        # <graph file> <attributes file> <resources file> <requirements> [<num ors> <# enums> <# numeric>]
        print 'Usage: {} <configuration file>'.format(sys.argv[0])
        sys.exit(-1)
               
    configFile = sys.argv[1]
    assert os.path.isfile(configFile)         
    config = ConfigParser.ConfigParser()
    config.read(configFile)
        
    structureFilename = config.get(SECTION_SYNTHESIS, OPTION_STRUCTURE)
    attributesFilename = config.get(SECTION_SYNTHESIS, OPTION_SUBJECT_ATTRIBUTES)
    resourcesFilename = config.get(SECTION_SYNTHESIS, OPTION_RESOURCE_ATTRIBUTES)
    reqsFilename = config.get(SECTION_SYNTHESIS, OPTION_REQUIREMENTS)
    outputFilename = config.get(SECTION_SYNTHESIS, OPTION_OUTPUT)
    isGrammarFixed = config.getboolean(SECTION_SYNTHESIS, OPTION_FIXED_GRAMMAR)

    assert os.path.isfile(structureFilename)
    assert os.path.isfile(attributesFilename)
    assert os.path.isfile(resourcesFilename)
    assert os.path.isfile(reqsFilename)
    assert os.path.isfile(outputFilename)
    
    print 'Resource structure filename:', structureFilename
    print 'Subject attributes filename:', attributesFilename
    print 'Resource attributes filename:', resourcesFilename
    print 'Requirements filename:', reqsFilename      

    graph = nx.read_adjlist(structureFilename, create_using = nx.DiGraph())    
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
        
    outputFile = open(outputFilename, 'w')

    if isGrammarFixed:
        num_ors = config.getint(SECTION_GRAMMAR, OPTION_NUMBER_OF_DISJUNCTIONS)
        num_enum = config.getint(SECTION_GRAMMAR, OPTION_NUMBER_OF_ENUMERATED_ATTRIBUTES)
        num_numeric = config.getint(SECTION_GRAMMAR, OPTION_NUMBER_OF_NUMERIC_ATTRIBUTES)
        policy = solve_synthesis_instance(reqsStr, num_ors, num_enum, num_numeric)
    else:        
        policy = unsat
        num_ors = 1
        num_enum = 0
        num_numeric = 0
        while policy == unsat:
            min_size = min(num_ors, num_enum, num_numeric)
            isIncremented = False
            if not isIncremented and num_ors == min_size:
                num_ors += 1
                isIncremented = True
            if not isIncremented and num_enum == min_size:
                num_enum += 1
                isIncremented = True
            if not isIncremented and num_numeric == min_size:
                num_numeric += 1
                isIncremented = True
            policy = solve_synthesis_instance(reqsStr, num_ors, num_enum, num_numeric)        
                                       
    if policy == unsat:
        print 'No solution was found'
    else:
        print '============ SYNTHESIZED POLICY ============'
        policyTable = []
        for edge in graph.edges():
            if edge[0] == edge[1]:
                continue
            check = policy[edge] if type(policy[edge]) == bool else policy[edge].sexpr()
            policyTable.append([edge[0], '->', edge[1], check])
        print tabulate(policyTable, headers = ['FROM', '', 'TO', 'LOCAL POLICY'])
    
    outputFile.close()