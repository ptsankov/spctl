'''
Created on May 2, 2016

@author: ptsankov
'''
import sys
import os

def measurePerformance():
    
    configs = {}
    
    configs['Airport'] = os.path.abspath('casestudies/airport/config')
    configs['Office'] = os.path.abspath('casestudies/office/config')
    configs['University'] = os.path.abspath('casestudies/university/config')
    