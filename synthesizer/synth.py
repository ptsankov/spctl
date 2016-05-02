#!/bin/python

'''
Created on May 17, 2015

@author: ptsankov
'''

from z3 import unsat
from tabulate import tabulate

import os
import ConfigParser
import static
from utils.helperMethods import log, setLogFile, closeLogFile, readResourceStructure
from synthesizer import conf
from utils import requirments_grammar, stats
from solver import template, smt
from synthesizer.utils import measurements
import math



def synth(configFilename): 
    #if len(sys.argv) != 2:
    #    print 'Usage: {} <configuration file>'.format(sys.argv[0])
    #    sys.exit(-1)
        
    #configFilename = sys.argv[1]
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
        subjAttrsStrs = f.readlines()
    conf.subjAttrs = [a.strip() for a in subjAttrsStrs]
    log('Attributes: ' + ', '.join(conf.subjAttrs))
    template.declareAttrVars()
    
    assert os.path.isfile(pepsFilename)    
    with open(pepsFilename) as f:
        pepStrs = f.readlines()
    conf.PEPS = [(x.split(' ')[0].strip(), (x.split(' ')[1].strip())) for x in pepStrs]
    log('PEPs: {}'.format(conf.PEPS))
    
    assert os.path.isfile(reqsFilename)
    with open(reqsFilename) as f:
        reqsStr = [x.strip() for x in f.readlines()]
        print reqsStr
    conf.reqs = [requirments_grammar.parseRequirement(x) for x in reqsStr if x.startswith('(')]    

    log('Number of requirements: ' + str(len(conf.reqs)))
    log('Number of resources: ' + str(len(conf.resourceStructure.nodes())))
    log('Number of PEPs: ' + str(len(conf.PEPS)))

    log('Starting synthesis...')

    policy = unsat
    template_size = 1
    while policy == unsat:
        log('Solve policy synthesis instance for template of size {}'.format(template_size))
        template.createTemplate(numOrs=template_size, numEnums=int(math.ceil(float(template_size)/2)), numNumeric=int(math.floor(float(template_size)/2)))
        policy = smt.solve()
        if policy == unsat:
            template_size += 1
                         
    log('Solution found for template ' + str(template_size))                           
                                       
    if policy == unsat:
        print 'No solution was found'
    else:
        print '============ SYNTHESIZED POLICY ============'
        policyTable = []
        for PEP in conf.PEPS:
            check = policy[PEP] if type(policy[PEP]) == bool else policy[PEP].sexpr()
            policyTable.append([PEP[0], '->', PEP[1], check])
        print tabulate(policyTable, headers = ['FROM', '', 'TO', 'LOCAL POLICY'])
    
    log('Time spend encoding SMT constraints: {}'.format(measurements.translation_time))
    log('Time spend solving constraints: {}'.format(measurements.smt_time))
    synthesis_time = measurements.smt_time + measurements.translation_time
    log('Total synthesis time: {}'.format(synthesis_time))
    
    closeLogFile()
    
    stats_map = {}
    stats_map[stats.TEMPLATE_SIZE] = template_size
    stats_map[stats.SYNTHESIS_TIME] = synthesis_time
    stats_map[stats.NUMBER_OF_REQUIREMENTS] = len(conf.reqs)
    stats_map[stats.NUMBER_OF_RESOURCES] = len(conf.resourceStructure.nodes())
    stats_map[stats.NUMBER_OF_PEPS] = len(conf.PEPS)
    stats_map[stats.LOG_FILE] = outputFilename
    return stats_map