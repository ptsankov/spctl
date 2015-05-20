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
    if len(sys.argv) != 4:
        print 'Usage: %s <graph file> <attributes file> <ctl file>'.format(sys.argv[0])
        sys.exit(-1)
        
    resGraphFilename = sys.argv[1]
    attributesFilename = sys.argv[2]
    ctlFilename = sys.argv[3]
    for filename in [resGraphFilename, attributesFilename, ctlFilename]:
        if not os.path.isfile(filename):
            print filename, 'is not a file'
            sys.exit(-1)    
        
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
                 
    for ctlFormula in ctlFormulas:
        print 'Processing CTL formula:', ctlFormula
        ctlToSAT(ctlFormula, resGraph, attrs)        