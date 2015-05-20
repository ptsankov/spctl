#!/usr/bin/python

'''
Created on May 17, 2015

@author: ptsankov
'''

import networkx as nx
import sys
import os

from ctl import ctlToSAT
from utils import declareRooms, setOutputFile
from utils.smt2Translation import declarePolicyTemplates

if __name__ == '__main__':
    if len(sys.argv) != 5:
        print 'Usage: {} <graph file> <attributes file> <ctl file> <output smt2 file>'.format(sys.argv[0])
        sys.exit(-1)
        
    resGraphFilename = sys.argv[1]
    attributesFilename = sys.argv[2]
    ctlFilename = sys.argv[3]
    outputFilename = sys.argv[4]
    for filename in [resGraphFilename, attributesFilename, ctlFilename]:
        if not os.path.isfile(filename):
            print filename, 'is not a file'
            sys.exit(-1)
    if os.path.isfile(outputFilename):
        msg = 'The output file "' + outputFilename + '" exists. Override?'
        shall = raw_input('{} (y/N) '.format(msg)).lower() == 'y'
        if not shall:
            sys.exit(-2)    
        
    print 'Resource graph filename:', resGraphFilename
    print 'Attributes filename:', attributesFilename
    print 'CTL filename:', ctlFilename
    
    resGraph = nx.read_adjlist(resGraphFilename, create_using = nx.DiGraph())    
    print 'Resource in the graph:', resGraph.nodes()
    
    with open(attributesFilename) as f:
        attrs = f.readlines()
    attrs = [a.strip() for a in attrs]
        
    for attr in attrs:
        print attr

    with open(ctlFilename) as f:
        ctlFormulas = f.readlines()
    ctlFormulas = [f.strip() for f in ctlFormulas]
    
    outFile = open(outputFilename, 'w')
    setOutputFile(outFile)
    
    declareRooms(resGraph)    
    declarePolicyTemplates(resGraph) 
                 
    for ctlFormula in ctlFormulas:
        print 'Processing CTL formula:', ctlFormula
        ctlToSAT(ctlFormula, resGraph, attrs)        