#!/usr/bin/python

'''
Created on May 17, 2015

@author: ptsankov
'''

import networkx as nx
import sys
import os

from ctl import ctlToSAT

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print 'Usage: %s <graph file> <ctl file>'.format(sys.argv[0])
        sys.exit(-1)
        
    resourceGraphFilename = sys.argv[1]
    ctlFilename = sys.argv[2]
    if not os.path.isfile(resourceGraphFilename):
        print resourceGraphFilename, 'is not a file'
        sys.exit(-2)
    if not os.path.isfile(ctlFilename):
        print ctlFilename, 'is not a file'
        sys.exit(-2)
        
    print 'Resource graph filename:', resourceGraphFilename
    print 'CTL filename:', ctlFilename
    
    
    resourceGraph = nx.read_adjlist(resourceGraphFilename, create_using = nx.DiGraph())    
    print 'Resource in the graph:', resourceGraph.nodes()

    with open(ctlFilename) as f:
         ctlFormulas = f.readlines()
         
    for ctlFormula in ctlFormulas:
        ctlFormula = ctlFormula.strip()
        print 'Processing CTL formula:', ctlFormula
        ctlToSAT(ctlFormula, resourceGraph)        