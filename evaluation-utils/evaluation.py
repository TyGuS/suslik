import sys
from subprocess import call
import os, os.path
import platform
import shutil
import csv

JAVA8        = 'java'                                             # Path to Java8
SUSLIK_JAR   = 'suslik.jar'                                       # Path to suslik.jar
TIMEOUT      = '-t=120000'                                        # Timeout option for suslik
TEST_DIR     = 'src/test/resources/synthesis/paper-benchmarks/'   # Root directory for the tests   
VARIANTS     = ['phased', 'invert', 'fail', 'commute', 'none']    # Configurations
CSV_IN       = 'stats.csv'                                        # Intermediate CSV file produced by suslik

STATS        = 'all_stats.csv'                                    # Output file with all the stats
RESULTS      = 'all_results'                                      # Output file with synthesis results

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
  def __init__(self, name, time, spec_size, code_size):
    self.name = name                                      # Benchmark name
    self.time = time                                      # Synthesis time (seconds)
    self.spec_size = spec_size                            # Cumulative specification size (in AST nodes)
    self.code_size = code_size                            # Cumulative synthesized code size (in AST nodes)
    self.variant_times = {var : -3.0 for var in VARIANTS} # Synthesis times for SuSLik variants:
      

  def str(self):
    return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', ' + self.spec_size + ', ' + self.code_size + ', ' + str(self.variant_times)

def run_benchmark(file):
  '''Run single benchmark'''
  with open(RESULTS, "a") as outfile:
    print 'Running', file
    call([JAVA8, '-jar', SUSLIK_JAR, file, TIMEOUT], stdout=outfile)
    read_csv()
    
def var_option(var):
  if var == 'none':
    return ' '.join([var_option(v) for v in VARIANTS[:-1]])
  else:
    return ' '.join(['--' + v + ' false' for v in var.split('-')])    

def test_variants():
  '''Test all enabled configurations of each benchmark'''
  
  for group in groups:
    for b in group.benchmarks:
      test = TEST_DIR + b.name
      testFileName = test + '.syn'
      if not os.path.isfile(testFileName):
        print "Test file not found:", testFileName
      else:
        run_benchmark(testFileName) # Run default configuration
      
        for var in variants:
          varFileName = test + '-' + var + '.syn'     
          shutil.copy(testFileName, varFileName)
          with open(varFileName, 'r+') as f:
            content = f.read()
            f.seek(0, 0)
            if content.startswith('#'):
              # already has a config line
              lines = content.split('\n', 1)
              f.write(lines[0].rstrip() + ' ' + var_option(var) + '\n' + lines[1])
            else:
              # no config line, create one
              f.write('#. ' + var_option(var) + '\n' + content)
              
          run_benchmark(varFileName) # Run variant
      
def clean_variants():
  '''Remove previously generated benchmark variants'''
  
  for group in groups:
    for b in group.benchmarks:
      test = TEST_DIR + b.name
      for var in VARIANTS:
        varFileName = test + '-' + var + '.syn'
        if os.path.isfile(varFileName):        
          os.remove(varFileName)
          
def read_csv():
  '''Read stats file into the results dictionary'''
  with open(CSV_IN, 'rb') as csvfile:
    d = csv.excel
    d.skipinitialspace = True
    statsReader = csv.DictReader(csvfile, dialect = d)
    for row in statsReader:
      name = row['Name']
      time = float(row['Time'])/1000
      spec_size = row['Spec Size']
      code_size = row['Code Size']
      
      is_var = False
      for var in VARIANTS:
        if name.endswith(var):
          # This is a test for a variant
          is_var = True
          suffix_len = len(var) + 1
          store_result(name[:-suffix_len], time, spec_size, code_size, var)
      if not is_var:
        store_result(name, time, spec_size, code_size)
        
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
    stats.write('Name,Code,Spec,Time,T-phase,T-inv,T-fail,T-com,T-all\n')
    
    for group in groups:
      for b in group.benchmarks:
        result = results[b.name]
        row = \
            b.name +\
            ',' + result.code_size + \
            ',' + result.spec_size + \
            ',' + format_time(result.time) + \
            ',' + format_time(result.variant_times['phased']) + \
            ',' + format_time(result.variant_times['invert']) + \
            ',' + format_time(result.variant_times['fail']) + \
            ',' + format_time(result.variant_times['commute']) + \
            ',' + format_time(result.variant_times['none']) + '\n'
        stats.write(row)
        
      
def store_result(name, time, spec_size, code_size, variant = 'all'):
  timeOrTO = -1.0 if code_size == 'FAIL' else time
  
  if not(name in results):
    results[name] = SynthesisResult(name, timeOrTO, spec_size, code_size)
  
  if variant == 'all':
    results[name].time = timeOrTO
    results[name].code_size = code_size
  else:
    results[name].variant_times[variant] = timeOrTO
          
def cmdline():
  import argparse
  a = argparse.ArgumentParser()
  a.add_argument('--unopt', action='store_true')
  a.add_argument('--tiny', action='store_true')
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
  test_variants()
  
  # print 'STATS'
  # for res in results:
    # print results[res].str()  
      
  write_stats()
  clean_variants()
  

