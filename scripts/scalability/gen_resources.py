import sys
import shutil
from shutil import copyfile

num_floors = int(sys.argv[1])

adjacency_file = 'kaba.adj'
resources_file = 'kaba.res'
requirements_file = 'kaba.reqs'

output_adjacency_file = open('kaba_' + str(num_floors) + '.adj', 'w')
output_resources_file = open('kaba_' + str(num_floors) + '.res', 'w')

resources = set()

lines = [x.strip() for x in open(adjacency_file).readlines()]
for i in range(num_floors):
    for l in lines:
        for r in l.split(' '):
            resources.add(r)
            if r == 'out' and i > 0:
                continue
            if r !=  'elev' and r != 'out':
                output_adjacency_file.write(r + '_' + str(i))
            else:
                output_adjacency_file.write(r)
            output_adjacency_file.write(' ')
        output_adjacency_file.write('\n')

output_adjacency_file.write('elev ')
for i in range(num_floors):
    output_adjacency_file.write('cor1_' + str(i) + ' ')  
    
for l in [x.strip() for x in open(resources_file).readlines()]:
    attrName = l.split('|')[0]
    output_resources_file.write(attrName + '|')
    rest = l.split('|')[1]
    for i in range(num_floors):
        output_resources_file.write(':'.join([x + '_' + str(i) if (not x.endswith('out') and not x.endswith('elev')) else x for x in rest.split(':')[:-1]]))
        output_resources_file.write(':' + rest.split(':')[-1])
        if i < num_floors - 1:
            output_resources_file.write(',')
    
output_resources_file.write('\n')

vals = []
for i in range(num_floors):
    for r in resources:
        if r != 'out' and r != 'elev':
            vals.append(r + '_' + str(i) + ':' + 'floor' + str(i))
        else:
            vals.append(r + ':' + 'floor' + str(i))

output_resources_file.write('floor|' + ','.join(vals) + '\n')


copyfile(requirements_file, 'kaba_' + str(num_floors) + '.reqs')

output_adjacency_file.close()
output_resources_file.close()