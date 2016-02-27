#!/bin/python

'''
Created on May 17, 2015

@author: ptsankov
'''

from z3 import unsat
from tabulate import tabulate

import sys
import os
import ConfigParser
import static
from utils.helperMethods import log, setLogFile, closeLogFile, readResourceStructure
import conf
from utils import requirments_grammar
from solver import template, smt



if __name__ == '__main__':
  
    if len(sys.argv) != 2:
        print 'Usage: {} <configuration file>'.format(sys.argv[0])
        sys.exit(-1)
               
    configFilename = sys.argv[1]
    assert os.path.isfile(configFilename)         
    config = ConfigParser.ConfigParser()
    config.read(configFilename)
    
    pathToFiles = os.path.dirname(os.path.realpath(configFilename))
        
    structureFilename = os.path.join(pathToFiles, config.get(static.SECTION_SYNTHESIS, static.OPTION_STRUCTURE))
    subjectAttributesFilename = os.path.join(pathToFiles, config.get(static.SECTION_SYNTHESIS, static.OPTION_SUBJECT_ATTRIBUTES))
    resourceAttributesFilename = os.path.join(pathToFiles, config.get(static.SECTION_SYNTHESIS, static.OPTION_RESOURCE_ATTRIBUTES))
    reqsFilename = os.path.join(pathToFiles, config.get(static.SECTION_SYNTHESIS, static.OPTION_REQUIREMENTS))
    pepsFilename = os.path.join(pathToFiles, config.get(static.SECTION_SYNTHESIS, static.OPTION_PEPS))
    outputFilename = os.path.join(pathToFiles, config.get(static.SECTION_SYNTHESIS, static.OPTION_OUTPUT))
    isGrammarFixed = config.getboolean(static.SECTION_SYNTHESIS, static.OPTION_FIXED_GRAMMAR)

    setLogFile(outputFilename)

    log('Resource structure filename: ' + structureFilename)
    log('Subject attributes filename: ' + subjectAttributesFilename)
    log('Resource attributes filename: ' + resourceAttributesFilename)
    log('Requirements filename: ' + reqsFilename)
    log('PEPs filename: ' + pepsFilename)
    log('Output file: ' + outputFilename)

    assert os.path.isfile(structureFilename)
    assert os.path.isfile(resourceAttributesFilename)    
    conf.resourceStructure = readResourceStructure(structureFilename, resourceAttributesFilename)
    
    assert os.path.isfile(subjectAttributesFilename)
    with open(subjectAttributesFilename) as f:
        subjAttrs = f.readlines()
    conf.subjAttrs = [a.strip() for a in subjAttrs]
    log('Attributes: ' + ', '.join(conf.subjAttrs))
    template.declareAttrVars()
    
    assert os.path.isfile(pepsFilename)    
    with open(pepsFilename) as f:
        pepStrs = f.readlines()
    conf.PEPS = [(x.split(' ')[0].strip(), (x.split(' ')[1].strip())) for x in pepStrs]
    
    assert os.path.isfile(reqsFilename)
    with open(reqsFilename) as f:
        reqsStr = [x.strip() for x in f.readlines()]
    conf.reqs = [requirments_grammar.parseRequirement(x) for x in reqsStr if x.startswith('(')]
    
        
    if isGrammarFixed:
        numOrs = config.getint(static.SECTION_GRAMMAR, static.OPTION_NUMBER_OF_DISJUNCTIONS)
        numEnums = config.getint(static.SECTION_GRAMMAR, static.OPTION_NUMBER_OF_ENUMERATED_ATTRIBUTES)
        numNumeric = config.getint(static.SECTION_GRAMMAR, static.OPTION_NUMBER_OF_NUMERIC_ATTRIBUTES)
                
        template.createTemplate(numOrs, numEnums, numNumeric)        
        policy = smt.solve() 
    else:
        policy = unsat
        numOrs = 1
        numEnums = 1
        numNumeric = 1
        while policy == unsat:
            template.createTemplate(numOrs, numEnums, numNumeric)
            min_size = min(numOrs, numEnums, numNumeric)
            if numEnums == min_size:
                numEnums += 1
            else:
                if numNumeric == min_size:
                    numNumeric += 1
                else:
                    numOrs += 1
            policy = smt.solve()                               
                                       
    if policy == unsat:
        print 'No solution was found'
    else:
        print '============ SYNTHESIZED POLICY ============'
        policyTable = []
        for PEP in conf.PEPS:
            check = policy[PEP] if type(policy[PEP]) == bool else policy[PEP].sexpr()
            policyTable.append([PEP[0], '->', PEP[1], check])
        print tabulate(policyTable, headers = ['FROM', '', 'TO', 'LOCAL POLICY'])
    
    log('DATA| Number of requirements: ' + str(len(reqs)))
    log('DATA| Number of resources: ' + str(len(conf.resourceStructure.nodes())))
    log('DATA| Number of enforcement points: ' + str(len(conf.PEPS)))

    
    closeLogFile()