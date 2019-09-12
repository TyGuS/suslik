# adapted of evaluation.py

import sys
from subprocess import call
import os, os.path
import platform
import shutil
import csv

JAVA8        = 'java'                                             # Path to Java8
SUSLIK_JAR   = 'target/scala-2.12/suslik.jar'                     # Path to suslik.jar
TIMEOUT      = '-t=120000'                                        # Timeout option for suslik
TEST_DIR     = 'src/test/resources/immutable-synthesis/regression/paper-benchmarks/old/'   # Root directory for the tests
VARIANTS     = ['phased', 'invert', 'fail', 'commute', 'none']    # Configurations
#CONFIG       = [('def', '')]                                     # Run with default configuration
CONFIG       = [('imm', '--imm true'),('mut', '--imm false')]     # Configurations -  add an empty string for default configuration
CSV_IN       = 'stats.csv'                                        # Intermediate CSV file produced by suslik

STATS        = 'evaluation-utils/all_stats.csv'                   # Output file with all the stats
RESULTS      = 'evaluation-utils/all_results'                     # Output file with synthesis results


class Benchmark:
  def __init__(self, name, description):
    self.name = name                # Test file name
    self.description = description  # Description (in the table)

  def str(self):
    return self.name + ': ' + self.description

class BenchmarkGroup:
  def __init__(self, name, benchmarks):
    self.name = name              # Id
    self.benchmarks = benchmarks  # List of benchmarks in this group

ALL_BENCHMARKS = [
  BenchmarkGroup("Integers",  [
    Benchmark('ints/swap', 'swap two'),
    Benchmark('ints/min2', 'min of two'),
    ]),    
  BenchmarkGroup("Linked List", [
    Benchmark('sll-bounds/sll-len', 'length'),
    Benchmark('sll-bounds/sll-max', 'max'),
    Benchmark('sll-bounds/sll-min', 'min'),
    Benchmark('sll/sll-singleton', 'singleton'),
    Benchmark('sll/sll-free', 'dispose'),
    Benchmark('sll/sll-init', 'initialize'),
    Benchmark('sll/sll-copy', 'copy'),
    Benchmark('sll/sll-append', 'append'),
    Benchmark('sll/sll-delete-all', 'delete'),
    ]),
  BenchmarkGroup("Sorted list", [
    Benchmark('srtl/srtl-prepend', 'prepend'),
    Benchmark('srtl/srtl-insert', 'insert'),
    Benchmark('srtl/insertion-sort', 'insertion sort'),
    ]),
  BenchmarkGroup("Tree", [
    Benchmark('tree/tree-size', 'size'),
    Benchmark('tree/tree-free', 'dispose'),
    Benchmark('tree/tree-copy', 'copy'),
    Benchmark('tree/tree-flatten', 'flatten w/append'),
    Benchmark('tree/tree-flatten-acc', 'flatten w/acc'),
    ]),
  BenchmarkGroup("BST", [
    Benchmark('bst/bst-insert', 'insert'),
    Benchmark('bst/bst-left-rotate', 'rotate left'),
    Benchmark('bst/bst-right-rotate', 'rotate right'),
    ]),
]

class SynthesisResult:
  def __init__(self, name, time, spec_size, code_size, backtracking, rules):
    self.name = name                                      # Benchmark name
    self.time = time                                      # Synthesis time (seconds)
    self.spec_size = spec_size                            # Cumulative specification size (in AST nodes)
    self.code_size = code_size                            # Cumulative synthesized code size (in AST nodes)
    self.variant_times = {var : -3.0 for var in VARIANTS} # Synthesis times for SuSLik variants:
    self.backtracking = backtracking                      # The number of times the synthesizer backtracked
    self.rules = rules                                    # The number of rules applied by the synthesizer
      

  def str(self):
    return '{0:0.2f}'.format(self.time) + ', ' + self.spec_size + ', ' + self.code_size + ', ' + self.backtracking + ', ' + self.rules

class SynthesisResultWrapper:
  def __init__(self, name):
     self.name = name
     self.res  = {cnf[0]: None for  cnf in CONFIG}

  def str(self):
      return self.name + "\n    " + ( ("\n    "). join([c[0] + " >> " + self.res[c[0]].str() for c in CONFIG]))

def run_benchmark(file, args):
  '''Run single benchmark'''
  with open(RESULTS, "a") as outfile:
    print 'Running ' + file + ' ' + (' '.join(args))
    call([JAVA8, '-jar', SUSLIK_JAR, file, TIMEOUT] + args, stdout=outfile)
    res_syn = read_csv()
    return res_syn

def test_configurations():
  '''Test all the configurations defined in CONFIG'''

  for group in groups:
    for b in group.benchmarks:
      test = TEST_DIR + b.name
      testFileName = test + '.syn'
      if not os.path.isfile(testFileName):
        print "Test file not found:", testFileName
      else:
        results[b.name] = SynthesisResultWrapper(b.name)
        for conf in CONFIG:
            args          = conf[1].split(' ')
            res_one_conf  = run_benchmark(testFileName,args) # Run default configuration
            results[b.name].res[conf[0]] = res_one_conf

def read_csv():
  '''Read stats file into the results dictionary'''
  with open(CSV_IN, 'rb') as csvfile:
    d = csv.excel
    d.skipinitialspace = True
    statsReader = csv.DictReader(csvfile, dialect = d)
    row = next(statsReader) #assumes that the csv contains stats about one single file
    name = row['Name']
    time = float(row['Time'])/1000
    spec_size = row['Spec Size']
    code_size = row['Code Size']
    backtracking = row['Backtrackings']
    rules = row['Applications']
    syn_res = store_result(name, time, spec_size, code_size, backtracking, rules)
    return syn_res


def format_time(t):
  if t < 0:
    return '-'
  if t < 0.1:
    return '<0.1'
  else:
    return '{0:0.1f}'.format(t)        
        

def write_stats():
  '''Write stats from dictionary into a file'''
  with open(STATS, 'w') as stats:
    headings = ['Code','Spec','Time','Backtrackings','Rules']     #configuration dependent headings
    new_headings = dict()
    for header in headings:
       new_headings[header] = {c[0]: (header + '(' + c[0] + ')') for c in CONFIG}  # creates a header for each conf
    complete_headings = 'Name,' + ( ','.join([ (",".join([new_headings[header][c[0]] for c in CONFIG])) for header in headings] ))
    stats.write(complete_headings+'\n')

    for group in groups:
      for b in group.benchmarks:
        result = results[b.name]
        row = \
            b.name +\
            ',' + (','.join([result.res[c[0]].code_size for c in CONFIG])) + \
            ',' + (','.join([result.res[c[0]].spec_size for c in CONFIG])) + \
            ',' + (','.join([format_time(result.res[c[0]].time) for c in CONFIG])) + \
            ',' + (','.join([result.res[c[0]].backtracking for c in CONFIG])) + \
            ',' + (','.join([result.res[c[0]].rules for c in CONFIG])) + \
            '\n'
        stats.write(row)

def store_result(name, time, spec_size, code_size, backtracking, rules, variant = 'all'):
  timeOrTO = -1.0 if code_size == 'FAIL' else time
  syn_res  = SynthesisResult(name, timeOrTO, spec_size, code_size, backtracking, rules)
  return syn_res
      

def cmdline():
  import argparse
  a = argparse.ArgumentParser()
  a.add_argument('--unopt', action='store_true')
  a.add_argument('--tiny', action='store_true')
  a.add_argument('--stats',action='store_true')
  return a.parse_args()          
          
if __name__ == '__main__':
  cl_opts = cmdline()
  
  if os.path.isfile(RESULTS):        
    os.remove(RESULTS)
    
  if cl_opts.unopt:
    variants = VARIANTS
  else:
    variants = []
    
  if cl_opts.tiny:
    groups = ALL_BENCHMARKS[0:1]
  else:
    groups = ALL_BENCHMARKS

  results = dict()
  test_configurations()

  if cl_opts.stats:
    print 'STATS'
    for res in results:
        print results[res].str()


  write_stats()

  

