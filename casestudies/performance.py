'''
Created on May 2, 2016

@author: ptsankov
'''
from tabulate import tabulate
import os
import shutil
from synthesizer import synth
from synthesizer.utils import stats
import statistics

LOG_DIR = os.path.abspath('casestudies/logs')
NUM_RUNS = 10

def measurePerformance():
    
    configs = {}
    
    configs['Airport'] = os.path.abspath('casestudies/airport/conf')
    configs['Office'] = os.path.abspath('casestudies/office/conf')
    configs['University'] = os.path.abspath('casestudies/university/conf')
    
    if os.path.exists(LOG_DIR):
        shutil.rmtree(LOG_DIR)
    
    os.mkdir(LOG_DIR)
    
    data = {}
    case_studies = list(configs.keys())
    for case_study in case_studies:
        data[case_study] = {}
        data[case_study][stats.SYNTHESIS_TIME] = []
        for i in range(NUM_RUNS):
            stats_map = synth.synth(configs[case_study])
            data[case_study][stats.SYNTHESIS_TIME].append(stats_map[stats.SYNTHESIS_TIME])
            data[case_study][stats.NUMBER_OF_PEPS] = stats_map[stats.NUMBER_OF_PEPS]
            data[case_study][stats.NUMBER_OF_REQUIREMENTS] = stats_map[stats.NUMBER_OF_REQUIREMENTS]
            data[case_study][stats.NUMBER_OF_RESOURCES] = stats_map[stats.NUMBER_OF_RESOURCES]
            dst_log_file = os.path.join(LOG_DIR, '{}_run{}.log'.format(case_study, i))
            shutil.copyfile(stats_map[stats.LOG_FILE], dst_log_file)
    
    print data
    
    table = []
    table.append(['Metric'] + configs.keys())
    table.append(['Number of requirements'] + [data[case_study][stats.NUMBER_OF_REQUIREMENTS] for case_study in case_studies])
    table.append(['Number of PEPs'] + [data[case_study][stats.NUMBER_OF_PEPS] for case_study in case_studies])
    table.append(['Number of subspaces'] + [data[case_study][stats.NUMBER_OF_RESOURCES] for case_study in case_studies])
    table.append(['Synthesis time (mean)'] + [statistics.mean(data[case_study][stats.SYNTHESIS_TIME]) for case_study in case_studies])
    table.append(['Synthesis time (stdev)'] + [statistics.stdev(data[case_study][stats.SYNTHESIS_TIME]) for case_study in case_studies])
    
    
    print tabulate(table, headers="firstrow")