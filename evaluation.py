import sys
from subprocess import call
import os, os.path
import platform
import shutil
import csv
from colorama import init, Fore, Back, Style

JAVA8         = 'java'                                             # Path to Java8
JAVA_OPTS     = ['-Xmx4G']                                         # Java options: increase max heap size
SUSLIK_JAR    = './target/scala-2.12/suslik.jar'                   # Path to suslik.jar
TEST_DIR      = 'src/test/resources/synthesis'                     # Parent directory for benchmarks
COMPLEX_DIR   = 'cyclic-benchmarks'                                # Subdirectory for complex benchmarks
SIMPLE_DIR    = 'simple-benchmarks'                                # Subdirectory for simple benchmarks
CSV_IN        = 'stats.csv'                                        # Intermediate CSV file produced by suslik

COMPLEX_STATS = 'complex.csv'                                      # Output stats file for complex benchmarks
SIMPLE_STATS  = 'simple.csv'                                       # Output stats file for simple benchmarks
RESULTS       = 'all_results'                                      # Output file with all synthesis results

class Benchmark:
  def __init__(self, name, description, category = ''):
    self.name = name                # Test file name
    self.description = description  # Description (in the table)
    self.category = category

  def str(self):
    return self.name + ': ' + self.description

class BenchmarkGroup:
  def __init__(self, name, benchmarks):
    self.name = name              # Id
    self.benchmarks = benchmarks  # List of benchmarks in this group
    
COMPLEX_BENCHMARKS = [
  BenchmarkGroup("Singly Linked List", [
    Benchmark('sll/free2', 'singly-linked list: deallocate two', category='tiny'),
    Benchmark('sll/multi-append', 'singly-linked list: append three'),
    Benchmark('sll/append-copy', 'singly-linked list: non-destructive append'),
    Benchmark('sll/union', 'singly-linked list: union'),
    Benchmark('sll/intersect', 'singly-linked list: intersection (non-destructive)', category='slow'),
    Benchmark('sll/diff', 'singly-linked list: difference'),
    Benchmark('sll/unique', 'singly-linked list: deduplicate'),
    ]),
  BenchmarkGroup("List of Lists", [
    Benchmark('multi-list/free', 'list of lists: deallocate', category='tiny'),
    Benchmark('multi-list/flatten', 'list of lists: flatten'),
    ]),
  BenchmarkGroup("Binary Tree", [
    Benchmark('tree/free2', 'binary tree: deallocate two', category='tiny'),
    Benchmark('tree/flatten', 'binary tree: flatten'),
    Benchmark('tree/flatten-dll', 'binary tree: flatten to dll in place'),
    ]),
  BenchmarkGroup("Rose Tree", [
    Benchmark('rose-tree/free', 'rose tree: deallocate', category='tiny'),
    Benchmark('rose-tree/flatten', 'rose tree: flatten'),
    ]),
  BenchmarkGroup("Sorted list", [
    Benchmark('srtl/reverse', 'sorted list: reverse'),
    Benchmark('srtl/sort', 'sorted list: sort'),
    Benchmark('srtl/merge', 'sorted list: merge'),
    ]),
  BenchmarkGroup("BST", [
    Benchmark('bst/list-to-bst', 'bst: from list'),
    Benchmark('bst/bst-to-srtl', 'bst: to sorted list'),
    ]),
]
    

SIMPLE_BENCHMARKS = [
  BenchmarkGroup("Integers",  [
    Benchmark('ints/swap', 'swap two'),
    Benchmark('ints/min2', 'min of two'),
    ]),    
  BenchmarkGroup("Singly Linked List", [
    Benchmark('sll-bounds/len', 'singly-linked list: length'),
    Benchmark('sll-bounds/max', 'singly-linked list: max'),
    Benchmark('sll-bounds/min', 'singly-linked list: min'),
    Benchmark('sll/free', 'singly-linked list: dispose'),
    Benchmark('sll/init', 'singly-linked list: initialize'),
    Benchmark('sll/copy', 'singly-linked list: copy'),
    Benchmark('sll/append', 'singly-linked list: append'),
    Benchmark('sll/singleton', 'singly-linked list: singleton'),
    Benchmark('sll/delete-all', 'singly-linked list: delete all occurrences'),
    ]),
  BenchmarkGroup("Sorted list", [
    Benchmark('srtl/prepend', 'sorted list: prepend'),
    Benchmark('srtl/insert', 'sorted list: insert'),
    Benchmark('srtl/insertion-sort', 'sorted list: insertion sort w/insert'),
    ]),
  BenchmarkGroup("Tree", [
    Benchmark('tree/size', 'tree: size'),
    Benchmark('tree/free', 'tree: dispose'),
    Benchmark('tree/copy', 'tree: copy'),
    Benchmark('tree/flatten-helper', 'tree: flatten w/append'),
    Benchmark('tree/flatten-acc', 'tree: flatten w/acc'),
    ]),
  BenchmarkGroup("BST", [
    Benchmark('bst/insert', 'bst: insert'),
    Benchmark('bst/left-rotate', 'bst: rotate left'),
    Benchmark('bst/right-rotate', 'bst: rotate right'),
    Benchmark('bst/delete-root', 'bst: delete root', category='slow'),
    ]),
  BenchmarkGroup("Doubly Linked List", [
    Benchmark('dll/copy', 'doubly-linked list: copy'),
    Benchmark('dll/append', 'doubly-linked list: append'),
    Benchmark('dll/delete-all', 'doubly-linked list: delete all occurrences'),
    Benchmark('dll/from-sll', 'doubly-linked list: from singly-linked'),
    ]),
]

class SynthesisResult:
  def __init__(self, name, time, spec_size, code_size, num_procs, num_stmt):
    self.name = name             # Benchmark name
    self.time = time             # Synthesis time (seconds)
    self.spec_size = spec_size   # Cumulative specification size (in AST nodes)
    self.code_size = code_size   # Cumulative synthesized code size (in AST nodes)
    self.num_procs = num_procs   # Number of procedures generated
    self.num_stmt = num_stmt     # Cumulative number of statements in generated code
      

  def str(self):
    return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', ' + self.spec_size + ', ' + self.code_size

def run_benchmark(file):
  '''Run single benchmark'''
  with open(RESULTS, "a") as outfile:
    print 'Running', file,
    sys.stdout.flush()
    call([JAVA8] + JAVA_OPTS + ['-jar', SUSLIK_JAR, file], stdout=outfile, stderr=outfile)
    read_csv()
    print
    
    
def run_all(groups, prefix):
  '''Test all benchmarks in groups in directory prefix'''
  
  for group in groups:
    for b in group.benchmarks:
      if b.category in cats_to_test:
        test = os.path.join(TEST_DIR, prefix, b.name)
        testFileName = test + '.syn'
        if not os.path.isfile(testFileName):
          print "Test file not found:", testFileName
        else:
          run_benchmark(testFileName)
          
def read_csv():
  '''Read stats file into the results dictionary'''
  with open(CSV_IN, 'rb') as csvfile:
    d = csv.excel
    d.skipinitialspace = True
    statsReader = csv.DictReader(csvfile, dialect = d)
    for row in statsReader:
      name = row['Name']
      time = float(row['Time'])/1000
      num_procs = row['Num Procs']
      num_stmt = row['Num Statements']
      spec_size = row['Spec Size']
      code_size = row['Code Size']
      store_result(name, time, spec_size, code_size, num_procs, num_stmt)
      if num_procs == 'FAIL':
        printerr('FAIL')
      else:
        printok(format_time(time) + 's')
        
def format_time(t):
  if t < 0:
    return '-'
  if t < 0.1:
    return '<0.1'
  else:
    return '{0:0.1f}'.format(t)

def format_ratio(m, n, precision = 1):
  if m < 0:
    return '-'
  else:
    return ('{0:0.' + str(precision) + 'f}').format(m/n) + 'x'    
    
def format_code(n):
  if n <= 0:
    return '-'
  else:
    return str(n)     
        
def write_stats(groups, out_file):
  '''Write stats from dictionary into a file'''
  with open(out_file, 'w') as stats:
    stats.write('Id,Description,Proc,Stmt,Code,Code/Spec,Time(sec)\n')
    
    all_benchmarks = sum([g.benchmarks for g in groups], [])
        
    for group in groups:
      for b in group.benchmarks:
        if b.name in results:
          result = results[b.name]
          row = \
              str(all_benchmarks.index(b) + 1) +\
              ',' + b.description +\
              ',' + format_code(result.num_procs) + \
              ',' + format_code(result.num_stmt) + \
              ',' + format_code(result.code_size) + \
              ',' + format_ratio(float(result.code_size), float(result.spec_size)) + \
              ',' + format_time(result.time) + '\n'
          stats.write(row)          
              
def store_result(name, time, spec_size, code_size, num_procs, num_stmt):  
  if num_procs == 'FAIL':
    # Benchmark failed
    results[name] = SynthesisResult(name, -1.0, spec_size, -1, -1, -1)
  else:
    results[name] = SynthesisResult(name, time, spec_size, code_size, num_procs, num_stmt)
    
def printerr(str):
    print (Back.RED + Fore.RED + Style.BRIGHT + str + Style.RESET_ALL),

def printok(str):
    print (Back.GREEN + Fore.GREEN + Style.BRIGHT + str + Style.RESET_ALL),

def printwarn(str):
    print (Back.YELLOW + Fore.YELLOW + Style.BRIGHT + str + Style.RESET_ALL),   
          
def cmdline():
  import argparse
  a = argparse.ArgumentParser()  
  a.add_argument('--tiny', action='store_true')
  a.add_argument('--simple', action='store_true')
  a.add_argument('--all', action='store_true')
  a.add_argument('--clean', action='store_true')
  return a.parse_args()          
          
if __name__ == '__main__':
  init()
  cl_opts = cmdline()
  
  # Clean up files created by this script:
  if os.path.isfile(RESULTS):        
    os.remove(RESULTS)
  if os.path.isfile(COMPLEX_STATS):        
    os.remove(COMPLEX_STATS)
  if os.path.isfile(SIMPLE_STATS):        
    os.remove(SIMPLE_STATS)
  # If asked explicitly, clean up suslik output and exit  
  if cl_opts.clean: 
    if os.path.isfile(CSV_IN):
      os.remove(CSV_IN)
    sys.exit(0)
  
  if cl_opts.tiny:
    cats_to_test = ['tiny']
  elif cl_opts.all:
    cats_to_test = ['', 'tiny', 'slow']  
  else:
    cats_to_test = ['', 'tiny']
          
  results = dict()  
  
  if not cl_opts.simple or cl_opts.all:
    run_all(COMPLEX_BENCHMARKS, COMPLEX_DIR)
    write_stats(COMPLEX_BENCHMARKS, COMPLEX_STATS)
  
  if cl_opts.simple or cl_opts.all:
    run_all(SIMPLE_BENCHMARKS, SIMPLE_DIR)
    write_stats(SIMPLE_BENCHMARKS, SIMPLE_STATS)
      
    
  

