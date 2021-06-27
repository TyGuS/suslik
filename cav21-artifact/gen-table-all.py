import sys
import os, os.path
import platform
import shutil
import time
import csv

# Globals
CSV_FILE = 'stats_all.csv'                                    # CSV-input file
LATEX_FILE = 'results.tex'                                    # Latex-output file
PAPER_DIR = '/mnt/h/Work/papers/synsl/challenges/current/tab' # Directory where to copy the latex file (if exists)
SOURCES = ['jennisys', 'natural', 'dryad', 'eguchi', 'new']
TIMEOUT = 1800

class Benchmark:
  def __init__(self, name, description, source=[], marks=[]):
    self.name = name        # Id (corresponds to test file name)
    self.description = description  # Description (in the table)
    self.source = source      # Where is this benchmark from (in the table)

  def str(self):
    return self.name + ': ' + self.description

class BenchmarkGroup:
  def __init__(self, name, benchmarks):
    self.name = name            # Id
    self.benchmarks = benchmarks      # List of benchmarks in this group

BENCHMARKS = [
  BenchmarkGroup("Integers",  [
    Benchmark('ints/swap', 'swap two', ['suslik']),
    Benchmark('ints/min2', 'min of two', ['suslik','jennisys']),
    ]),    
  BenchmarkGroup("Singly Linked List", [
    Benchmark('sll/len', 'length', ['suslik','natural']),
    Benchmark('sll/max', 'max', ['suslik','natural']),
    Benchmark('sll/min', 'min', ['suslik','natural']),
    Benchmark('sll/singleton', 'singleton', ['suslik', 'jennisys']),
    Benchmark('sll/free', 'deallocate', ['suslik']),
    Benchmark('sll/init', 'initialize', ['suslik']),
    Benchmark('sll/copy', 'copy', ['suslik','dryad']),
    Benchmark('sll/append', 'append', ['suslik','dryad']),
    Benchmark('sll/delete-all', 'delete', ['suslik','dryad']),
    Benchmark('sll/free2', 'deallocate two'),
    Benchmark('sll/multi-append', 'append three'),
    Benchmark('sll/append-copy', 'non-destructive append'),
    Benchmark('sll/union', 'union'),
    Benchmark('sll/intersect', 'intersection', ['eguchi']),
    Benchmark('sll/diff', 'difference', ['eguchi']),
    Benchmark('sll/unique', 'deduplicate', ['eguchi']),
    ]),
  BenchmarkGroup("Sorted list", [
    Benchmark('srtl/prepend', 'prepend', ['suslik','natural']),
    Benchmark('srtl/insert', 'insert', ['suslik','natural']),
    Benchmark('srtl/insertion-sort', 'insertion sort', ['suslik','natural']),
    Benchmark('srtl/sort', 'sort', ['eguchi']),
    Benchmark('srtl/reverse', 'reverse', ['eguchi']),
    Benchmark('srtl/merge', 'merge', ['natural']),
    ]),    
  BenchmarkGroup("Doubly Linked List", [
    Benchmark('dll/singleton', 'singleton', ['jennisys']),  
    Benchmark('dll/copy', 'copy'),
    Benchmark('dll/append', 'append', ['dryad']),
    Benchmark('dll/delete-all', 'delete', ['dryad']),
    Benchmark('dll/from-sll', 'single to double'),    
  ]),        
  BenchmarkGroup("List of Lists", [
    Benchmark('multi-list/free', 'deallocate'),
    Benchmark('multi-list/flatten', 'flatten', ['eguchi']),
    Benchmark('multi-list/len', 'length', ['new']),
    ]),    
  BenchmarkGroup("Binary Tree", [
    Benchmark('tree/size', 'size', ['suslik']),
    Benchmark('tree/free', 'deallocate', ['suslik']),
    Benchmark('tree/free2', 'deallocate two'),
    Benchmark('tree/copy', 'copy', ['suslik']),
    Benchmark('tree/flatten-helper', 'flatten w/append', ['suslik']),
    Benchmark('tree/flatten-acc', 'flatten w/acc', ['suslik']),
    Benchmark('tree/flatten', 'flatten'),
    Benchmark('tree/flatten-dll', 'flatten to dll in place'),
    Benchmark('tree/flatten-dll-linear', 'flatten to dll w/null', ['new']),
    ]),
  BenchmarkGroup("BST", [
    Benchmark('bst/insert', 'insert', ['suslik','natural']),
    Benchmark('bst/left-rotate', 'rotate left', ['suslik','natural']),
    Benchmark('bst/right-rotate', 'rotate right', ['suslik','natural']),
    Benchmark('bst/min', 'find min', ['new']),
    Benchmark('bst/max', 'find max', ['new']),
    Benchmark('bst/delete-root', 'delete root', ['natural']),
    Benchmark('bst/list-to-bst', 'from list', ['eguchi']),
    Benchmark('bst/to-srtl', 'to sorted list', ['eguchi']),
    ]),
  BenchmarkGroup("Rose Tree", [
    Benchmark('rose-tree/free', 'deallocate'),
    Benchmark('rose-tree/flatten', 'flatten'),
    Benchmark('rose-tree/copy', 'copy', ['new']),
    ]),
  BenchmarkGroup("Packed Tree", [
    Benchmark('packed/pack', 'pack', ['new']),
    Benchmark('packed/unpack', 'unpack', ['new']),
    ]),    
]

class SynthesisResult:
  def __init__(self, name, time, spec_size, num_procs, code_size, statements):
    self.name = name                                      # Benchmark name
    self.time = time                                      # Synthesis time (seconds)
    self.spec_size = spec_size                            # Cumulative specification size (in AST nodes)
    self.num_procs = num_procs                            # Number of generated recursive procedures
    self.code_size = code_size                            # Cumulative synthesized code size (in AST nodes)
    self.statements = statements                          # Number of statements      

  def str(self):
    return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', ' + self.spec_size + ', ' + self.code_size + ', ' + str(self.variant_times)

    
def format_time(t):
  if t < 0:
    return '-'
  if t < 0.1:
    return '$<0.1$'
  else:
    return '{0:0.1f}'.format(t)
    
def format_ratio(m, n, precision = 1):
  if m < 0.0:
    return ''
  else:
    return ('{0:0.' + str(precision) + 'f}').format(m/n) + 'x'
    
def format_code(n):
  if n <= 0:
    return '-'
  else:
    return str(n)    

def read_csv():
  '''Read stats file into the results dictionary'''
  with open(CSV_FILE, 'rb') as csvfile:
    d = csv.excel
    d.skipinitialspace = True
    statsReader = csv.DictReader(csvfile, dialect = d)
    for row in statsReader:
      name = row['Name']
      time = float(row['Time'])/1000
      time_simple_cost = float(row['Time simple cost'])/1000
      time_no_limits = float(row['Time no limits'])/1000
      spec_size = row['Spec Size']
      num_procs = row['Num Procs']
      code_size = row['Code Size']
      statements = row['Num Statements']
      
      store_result(name, time, spec_size, num_procs, code_size, statements, time_simple_cost, time_no_limits)
      
def timeOrTO(time): 
  return -1.0 if time >= TIMEOUT else time  
      
def store_result(name, time, spec_size, num_procs, code_size, statements, time_simple_cost, time_no_limits):
  results[name] = SynthesisResult(name, timeOrTO(time), spec_size, num_procs, code_size, statements)
  results[name].time_simple_cost = timeOrTO(time_simple_cost)
  results[name].time_no_limits = timeOrTO(time_no_limits)
  
def footnotes(sources):
  res = []
  for s in sources:
    if s in SOURCES:      
      res += str(SOURCES.index(s) + 1)
  
  if res == []:
    return ''
  else:
    return '\\textsuperscript{' + ','.join(res) + '}'
  

def write_latex():
  '''Generate Latex table from the results dictionary'''
  
  total_count = 0
  # to_count = {var : 0 for var in VARIANTS}

  with open(LATEX_FILE, 'w') as outfile:
    for group in groups:
      outfile.write ('\multirow{')
      outfile.write (str(group.benchmarks.__len__()))
      outfile.write ('}{*}{{{')
      # outfile.write ('}{*}{\\parbox{2cm}{\center{')
      outfile.write (group.name)
      outfile.write ('}}}')      

      for b in group.benchmarks:
        total_count = total_count + 1
        result = results [b.name]        
        row = \
          ' & ' + str(total_count) +\
          ' & ' + b.description + footnotes(b.source) +\
          ' & ' + result.num_procs + \
          ' & ' + result.statements + \
          ' & ' + format_ratio(float(result.code_size), float(result.spec_size)) + \
          ' & ' + format_time(result.time) + \
          ' & ' + format_time(result.time_simple_cost) + \
          ' & ' + format_time(result.time_no_limits)  + ' \\\\'         
          
        outfile.write (row)
        outfile.write ('\n')        
        
      outfile.write ('\\hline')
      
  # Copy latex file into the paper directory if properly set
  if os.path.isdir(PAPER_DIR):
    shutil.copy(LATEX_FILE, PAPER_DIR)
  else:
    print 'Paper not found in ', PAPER_DIR  
      
  print 'Total:', total_count
            

if __name__ == '__main__':
  # init()
  
  
  results = dict()
  groups = BENCHMARKS
  read_csv()
  write_latex()
    
    

    
