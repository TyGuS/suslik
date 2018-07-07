import sys
import os, os.path
import platform
import shutil
import time
# import re
import csv
# from subprocess import call, check_output, STDOUT
# from colorama import init, Fore, Back, Style

# Globals
CSV_FILE = 'stats.csv'                                        # CSV-input file
LATEX_FILE = 'results.tex'                                    # Latex-output file
PAPER_DIR = '/mnt/h/Work/papers/synsl/synsl/popl19-draft/tab' # Directory where to copy the latex file (if exists)

class Benchmark:
    def __init__(self, name, description, source=[]):
        self.name = name                # Id (corresponds to test file name)
        self.description = description  # Description (in the table)
        self.source = source            # Where is this benchmark from (in the table)

    def str(self):
        return self.name + ': ' + self.description

class BenchmarkGroup:
    def __init__(self, name, benchmarks):
        self.name = name                        # Id
        self.benchmarks = benchmarks            # List of benchmarks in this group

ALL_BENCHMARKS = [
    BenchmarkGroup("Linked List", [
        Benchmark('natural/sll-len', 'length', ['natural']),
        Benchmark('natural/sll-max', 'max', ['natural']),
        Benchmark('natural/sll-min', 'min', ['natural']),
        ]),
    # BenchmarkGroup("Strictly sorted list", ['-f=AllArguments'], [
        # Benchmark('StrictIncList-Insert', 'insert', '$<$'),
        # Benchmark('StrictIncList-Delete', 'delete', '$<$'),
        # Benchmark('StrictIncList-Intersect', 'intersect', '$<$', ['-f=AllArguments']),
        # ]),
    # BenchmarkGroup("Tree", [
        # Benchmark('tree/tree-size', 'size', []),
        # ]),
    # BenchmarkGroup("Integers",  [], [
        # Benchmark('Tree-Elem', 'is member', 'false, not, or, $=$'),
        # Benchmark('Tree-Count', 'node count', '0, 1, +'),
        # ]),        
]

class SynthesisResult:
    def __init__(self, name, time, spec_size, code_size):
        self.name = name                        # Benchmark name
        self.time = time                        # Synthesis time (seconds)
        self.spec_size = spec_size              # Cumulative specification size (in AST nodes)
        self.code_size = code_size              # Cumulative synthesized code size (in AST nodes)
        # self.variant_times = {                  # Synthesis times for SuSLik variants:
                                # 'pha': -3.0,         # no phases
                                # 'inv': -3.0,         # no invertible rules
                                # 'fail': -3.0,        # no early failure
                                # 'com': -3.0,         # no commutativity
                             # }

    def str(self):
        return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', ' + self.spec_size + ', ' + self.code_size

      
def format_time(t):
    if t < 0:
        return '-'
    else:
        return '{0:0.2f}'.format(t)

def read_csv():
    '''Read stats file into the results dictionary'''
    with open(CSV_FILE, 'rb') as csvfile:
        d = csv.excel
        d.skipinitialspace = True
        statsReader = csv.DictReader(csvfile, dialect = d)
        for row in statsReader:
            name = row['Name']
            results [name] = SynthesisResult(name, float(row['Time'])/1000, row['Spec Size'], row['Code Size'])   

def write_latex():
    '''Generate Latex table from the results dictionary'''
    
    total_count = 0
    # to_def = 0
    # to_nrt = 0
    # to_ncc = 0
    # to_nmus = 0

    with open(LATEX_FILE, 'w') as outfile:
        for group in groups:
            outfile.write ('\multirow{')
            outfile.write (str(group.benchmarks.__len__()))
            outfile.write ('}{*}{\\parbox{1cm}{\center{')
            outfile.write (group.name)
            outfile.write ('}}}')            

            for b in group.benchmarks:
                result = results [b.name]                
                row = \
                    ' & ' + b.description +\
                    ' & ' + result.spec_size + \
                    ' & ' + result.code_size + \
                    ' & ' + format_time(result.time) + ' \\\\'
                    # ' & ' + format_time(result.variant_times['def']) + \
                    # ' & ' + format_time(result.variant_times['nrt']) + \
                    # ' & ' + format_time(result.variant_times['ncc']) + \
                    # ' & ' + format_time(result.variant_times['nmus']) + \
                    
                outfile.write (row)
                outfile.write ('\n')
                
                total_count = total_count + 1
                # if result.variant_times['def'] < 0.0:
                   # to_def = to_def + 1 
                # if result.variant_times['nrt'] < 0.0:
                   # to_nrt = to_nrt + 1 
                # if result.variant_times['ncc'] < 0.0:
                   # to_ncc = to_ncc + 1 
                # if result.variant_times['nmus'] < 0.0:
                   # to_nmus = to_nmus + 1 
                
            outfile.write ('\\hline')
            
    print 'Total:', total_count
    # print 'TO def:', to_def
    # print 'TO nrt:', to_nrt
    # print 'TO ncc:', to_ncc
    # print 'TO nmus:', to_nmus
    

if __name__ == '__main__':
    # init()
    
    results = dict()
    groups = ALL_BENCHMARKS
                
    # Read stats into a dictionary of synthesis results
    read_csv()            
    # Generate Latex table
    write_latex()
    
    # Copy latex file into the paper directory if properly set
    if os.path.isdir(PAPER_DIR):
      shutil.copy(LATEX_FILE, PAPER_DIR)
    else:
      print 'Paper not found in ', PAPER_DIR

        