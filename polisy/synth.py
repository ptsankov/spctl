#!/bin/python

'''
Created on May 17, 2015

@author: ptsankov
'''
from z3 import unsat
from tabulate import tabulate

import networkx
import sys
import os
import ConfigParser
from networkx.classes.function import set_node_attributes
from static import OPTION_STRUCTURE, OPTION_SUBJECT_ATTRIBUTES,\
    OPTION_RESOURCE_ATTRIBUTES, SECTION_SYNTHESIS, OPTION_REQUIREMENTS,\
    OPTION_OUTPUT, OPTION_FIXED_GRAMMAR, OPTION_NUMBER_OF_DISJUNCTIONS,\
    SECTION_GRAMMAR, OPTION_NUMBER_OF_ENUMERATED_ATTRIBUTES,\
    OPTION_NUMBER_OF_NUMERIC_ATTRIBUTES, OPTION_PEPS
from utils.helperMethods import log, setLogFile, closeLogFile
from algorithms.smt import synthFixedGrammar, synth
from core import requirments_grammar
import conf


def getResourceStructure(graphFilename, resourceAttributesFilename):
    resourceStructure = networkx.read_adjlist(graphFilename, create_using = networkx.DiGraph())    
    log('Resources: ' + ', '.join(resourceStructure.nodes()))
    
    with open(resourceAttributesFilename) as f:
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
        set_node_attributes(resourceStructure, attrName, resAttrMap)
    resAttrMap = {}
    for n in resourceStructure.nodes():
        resAttrMap[n] = n
    set_node_attributes(resourceStructure, 'room_id', resAttrMap)
    return resourceStructure
    
if __name__ == '__main__':
    global outputFile
    
    if len(sys.argv) != 2:
        # <graph file> <attributes file> <resources file> <requirements> [<num ors> <# enums> <# numeric>]
        print 'Usage: {} <configuration file>'.format(sys.argv[0])
        sys.exit(-1)
               
    configFilename = sys.argv[1]
    assert os.path.isfile(configFilename)         
    config = ConfigParser.ConfigParser()
    config.read(configFilename)
    
    pathToFiles = os.path.dirname(os.path.realpath(configFilename))
        
    graphFilename = os.path.join(pathToFiles, config.get(SECTION_SYNTHESIS, OPTION_STRUCTURE))
    subjectAttributesFilename = os.path.join(pathToFiles, config.get(SECTION_SYNTHESIS, OPTION_SUBJECT_ATTRIBUTES))
    resourceAttributesFilename = os.path.join(pathToFiles, config.get(SECTION_SYNTHESIS, OPTION_RESOURCE_ATTRIBUTES))
    reqsFilename = os.path.join(pathToFiles, config.get(SECTION_SYNTHESIS, OPTION_REQUIREMENTS))
    pepsFilename = os.path.join(pathToFiles, config.get(SECTION_SYNTHESIS, OPTION_PEPS))
    outputFilename = os.path.join(pathToFiles, config.get(SECTION_SYNTHESIS, OPTION_OUTPUT))
    isGrammarFixed = config.getboolean(SECTION_SYNTHESIS, OPTION_FIXED_GRAMMAR)

    setLogFile(outputFilename)

    log('Resource structure filename: ' + graphFilename)
    log('Subject attributes filename: ' + subjectAttributesFilename)
    log('Resource attributes filename: ' + resourceAttributesFilename)
    log('Requirements filename: ' + reqsFilename)
    log('Output file: ' + outputFilename)

    assert os.path.isfile(graphFilename)
    assert os.path.isfile(resourceAttributesFilename)    
    resStructure = getResourceStructure(graphFilename, resourceAttributesFilename)
    
    assert os.path.isfile(subjectAttributesFilename)
    with open(subjectAttributesFilename) as f:
        subjAttrs = f.readlines()
    subjAttrs = [a.strip() for a in subjAttrs]
    log('Attributes: ' + ', '.join(subjAttrs))
    
    with open(pepsFilename) as f:
        pepStrs = f.readlines()
    conf.PEPS = [(x.split(' ')[0].strip(), (x.split(' ')[1].strip())) for x in pepStrs]
    
    assert os.path.isfile(reqsFilename)
    with open(reqsFilename) as f:
        reqsStr = [x.strip() for x in f.readlines()]
    reqs = [requirments_grammar.parseRequirement(x) for x in reqsStr if x.startswith('(')]
                
    if isGrammarFixed:
        num_ors = config.getint(SECTION_GRAMMAR, OPTION_NUMBER_OF_DISJUNCTIONS)
        num_enum = config.getint(SECTION_GRAMMAR, OPTION_NUMBER_OF_ENUMERATED_ATTRIBUTES)
        num_numeric = config.getint(SECTION_GRAMMAR, OPTION_NUMBER_OF_NUMERIC_ATTRIBUTES)
        policy = synthFixedGrammar(resStructure, reqs, subjAttrs, num_ors, num_enum, num_numeric) 
    else:        
        
        policy = synth(resStructure, reqs, subjAttrs)        
                                       
    if policy == unsat:
        print 'No solution was found'
    else:
        print '============ SYNTHESIZED POLICY ============'
        policyTable = []
        for enforcementPoint in conf.PEPS:
#            if enforcementPoint[0] == enforcementPoint[1]:
#                continue
            check = policy[enforcementPoint] if type(policy[enforcementPoint]) == bool else policy[enforcementPoint].sexpr()
            policyTable.append([enforcementPoint[0], '->', enforcementPoint[1], check])
        print tabulate(policyTable, headers = ['FROM', '', 'TO', 'LOCAL POLICY'])
    
    log('DATA| Number of requirements: ' + str(len(reqs)))
    log('DATA| Number of resources: ' + str(len(resStructure.nodes())))
    log('DATA| Number of enforcement points: ' + str(len(resStructure.edges())))

    
    closeLogFile()