'''
Created on May 2, 2016

@author: ptsankov
'''
from experiments.casestudies import performance
from experiments.scalability import scalability
from synthesizer import synth
import sys

def printUsage():
    print 'Usage'

if __name__ == '__main__':
    if len(sys.argv) < 2:
        printUsage()
        sys.exit(-1)
    if sys.argv[1] not in ['-synth', '-measure-performance']:
        printUsage()
        sys.exit(-1) 
    
    if sys.argv[1] == '-synth':
        synth.synth(sys.argv[2])
    elif sys.argv[1] == '-measure-performance':
        performance.measurePerformance()