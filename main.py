'''
Created on May 2, 2016

@author: ptsankov
'''
from synthesizer import synth
import sys


def printUsage():
    print 'Usage'

if __name__ == '__main__':
    if len(sys.argv) < 2:
        printUsage()
        sys.exit(-1)
    if sys.argv[1] not in ['-synth']:
        printUsage()
        sys.exit(-1) 
    
    if sys.argv[1] == '-synth':
        synth.synth(sys.argv[2])