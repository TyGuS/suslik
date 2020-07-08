import sys
import os, os.path
import platform
import shutil
import time
import csv

# Globals
CSV_FILE = 'stats.csv'                    # CSV-input file
LATEX_FILE = 'results.tex'                  # Latex-output file
OLD_LATEX_FILE = 'old_results.tex'          # Latex-output file
PAPER_DIR = '/mnt/h/Work/papers/synsl/cyclic/current/tab' # Directory where to copy the latex file (if exists)
TEST_DIR = 'src/test/resources/synthesis/cyclic-benchmarks/'
SOURCES = ['eguchi', 'natural', 'jennisys', 'dryad']
VARIANTS = ['memo', 'dfs', 'bfs']
# VARIANTS = ['phased', 'invert', 'fail', 'commute', 
            # 'phased-invert', 'phased-fail', 'phased-commute', 'invert-fail', 'invert-commute', 'fail-commute',
            # 'phased-invert-fail', 'phased-invert-commute', 'invert-fail-commute']
# VARIANTS = ['phased', 'invert', 'fail', 'commute', 'all']

class Benchmark:
  def __init__(self, name, description, source=[], stime=-3.0, scode=0, marks=[]):
    self.name = name        # Id (corresponds to test file name)
    self.description = description  # Description (in the table)
    self.source = source      # Where is this benchmark from (in the table)
    self.suslik_time = stime
    self.suslik_code = scode
    self.marks = marks

  def str(self):
    return self.name + ': ' + self.description

class BenchmarkGroup:
  def __init__(self, name, benchmarks):
    self.name = name            # Id
    self.benchmarks = benchmarks      # List of benchmarks in this group

NEW_BENCHMARKS = [    
  BenchmarkGroup("Singly Linked List", [
    Benchmark('sll/listfree2', 'deallocate two'),
    Benchmark('sll/multi-append', 'append three'),
    Benchmark('sll/append-copy', 'non-destructive append'),
    Benchmark('sll/intersect', 'intersection', ['eguchi']),
    Benchmark('sll/diff', 'difference', ['eguchi']),
    Benchmark('sll/unique', 'deduplicate', ['eguchi']),
    ]),
  BenchmarkGroup("List of Lists", [
    Benchmark('multi-list/multilist-free', 'deallocate'),
    Benchmark('multi-list/multilist-flatten', 'concatenate', ['eguchi']),
    ]),    
  BenchmarkGroup("Binary Tree", [
    Benchmark('tree/treefree2', 'deallocate two'),
    Benchmark('tree/tree-flatten', 'flatten into list'),
    ]),
  BenchmarkGroup("Rose Tree", [
    Benchmark('rose-tree/rose-tree-free', 'deallocate', marks=['M']),
    Benchmark('rose-tree/rose-tree-flatten', 'flatten into list', marks=['M']),
    ]),
  BenchmarkGroup("Sorted list", [
    Benchmark('srtl/reverse', 'reverse', ['eguchi']),
    Benchmark('srtl/sort', 'sort', ['eguchi']),
    Benchmark('srtl/srtl-merge', 'merge', ['natural'], marks=['T']),
    ]),
  BenchmarkGroup("BST", [
    Benchmark('bst/list-to-bst', 'from list', ['eguchi']),
    Benchmark('bst/bst-to-srtl', 'to sorted list', ['eguchi'], marks=['M']),
    ]),
]

OLD_BENCHMARKS = [
  BenchmarkGroup("Integers",  [
    Benchmark('ints/swap', 'swap two', stime=0.0, scode=12),
    Benchmark('ints/min2', 'min of two', ['jennisys'], stime=0.1, scode=10),
    ]),    
  BenchmarkGroup("Linked List", [
    Benchmark('sll-bounds/sll-len', 'length', ['natural'], stime=0.4, scode=21),
    Benchmark('sll-bounds/sll-max', 'max', ['natural'], stime=0.6, scode=27),
    Benchmark('sll-bounds/sll-min', 'min', ['natural'], stime=0.5, scode=27),
    Benchmark('sll/sll-singleton', 'singleton', ['jennisys'], stime=0.0, scode=11),
    Benchmark('sll/sll-free', 'dispose', stime=0.0, scode=11),
    Benchmark('sll/sll-init', 'initialize', stime=0.0, scode=13),
    Benchmark('sll/sll-copy', 'copy', ['dryad'], stime=0.2, scode=35),
    Benchmark('sll/sll-append', 'append', ['dryad'], stime=0.2, scode=19),
    Benchmark('sll/sll-delete-all', 'delete', ['dryad'], stime=0.7, scode=44),
    ]),
  BenchmarkGroup("Sorted list", [
    Benchmark('srtl/srtl-prepend', 'prepend', ['natural'], stime=0.2, scode=11),
    Benchmark('srtl/srtl-insert', 'insert', ['natural'], stime=4.8, scode=58),
    Benchmark('srtl/insertion-sort', 'insertion sort', ['natural'], stime=1.1, scode=28),
    ]),
  BenchmarkGroup("Tree", [
    Benchmark('tree/tree-size', 'size', stime=0.2, scode=38),
    Benchmark('tree/tree-free', 'dispose', stime=0.0, scode=16),
    Benchmark('tree/tree-copy', 'copy', stime=0.4, scode=55),
    Benchmark('tree/tree-flatten', 'flatten w/append', stime=0.4, scode=48),
    Benchmark('tree/tree-flatten-acc', 'flatten w/acc', stime=0.6, scode=35),
    ]),
  BenchmarkGroup("BST", [
    Benchmark('bst/bst-insert', 'insert', ['natural'], stime=31.9, scode=58),
    Benchmark('bst/bst-left-rotate', 'rotate left', ['natural'], stime=37.7, scode=15),
    Benchmark('bst/bst-right-rotate', 'rotate right', ['natural'], stime=17.2, scode=15),
    ]),
]

class SynthesisResult:
  def __init__(self, name, time, spec_size, num_procs, code_size, total_goals, backtracked):
    self.name = name                                      # Benchmark name
    self.time = time                                      # Synthesis time (seconds)
    self.spec_size = spec_size                            # Cumulative specification size (in AST nodes)
    self.num_procs = num_procs                            # Number of generated recursive procedures
    self.code_size = code_size                            # Cumulative synthesized code size (in AST nodes)
    self.total_goals = total_goals
    self.backtracked = backtracked
    self.variant_times = {var : -3.0 for var in VARIANTS} # Synthesis times for SuSLik variants:
    self.variant_total_goals = {var : '-' for var in VARIANTS}
    self.variant_backtracked = {var : '-' for var in VARIANTS}
      

  def str(self):
    return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', ' + self.spec_size + ', ' + self.code_size + ', ' + str(self.variant_times)

# SuSLik command-line options to run the variant var    
def var_option(var):
  if var == 'dfs':
    return '--dfs true'
  elif var == 'bfs':
    return '--bfs true'
  elif var == 'memo':
    return '--memo false'
    
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
    

def read_csv():
  '''Read stats file into the results dictionary'''
  with open(CSV_FILE, 'rb') as csvfile:
    d = csv.excel
    d.skipinitialspace = True
    statsReader = csv.DictReader(csvfile, dialect = d)
    for row in statsReader:
      name = row['Name']
      time = float(row['Time'])/1000
      spec_size = row['Spec Size']
      num_procs = row['Num Procs']
      code_size = row['Code Size']
      total_goals = row['Goals generated']
      backtracked = row['And-nodes backtracked']
      
      is_var = False
      for var in VARIANTS:
        if name.endswith(var):
          # This is a test for a variant
          is_var = True
          suffix_len = len(var) + 1
          store_result(name[:-suffix_len], time, spec_size, num_procs, code_size, total_goals, backtracked, var)
      if not is_var:
        store_result(name, time, spec_size, num_procs, code_size, total_goals, backtracked)
      
def store_result(name, time, spec_size, num_procs, code_size, total_goals, backtracked, variant = 'none'):
  timeOrTO = -1.0 if num_procs == 'FAIL' else time
  
  if not(name in results):
    results[name] = SynthesisResult(name, timeOrTO, spec_size, num_procs, code_size, total_goals, backtracked)
  
  if variant == 'none':
    results[name].time = timeOrTO
    results[name].total_goals = total_goals
    results[name].backtracked = backtracked
    results[name].num_procs = num_procs
    results[name].code_size = code_size
  else:
    results[name].variant_times[variant] = timeOrTO
    results[name].variant_total_goals[variant] = total_goals
    results[name].variant_backtracked[variant] = backtracked
      
def footnotes(sources):
  res = ''
  for s in sources:
    i = SOURCES.index(s) + 1
    res = res + '\\textsuperscript{' + str(i) + '}'
  return res  
  
def render_marks(marks):
  if marks == []:
    return ''
  else:
    mark_map = {'M' : '$\dagger$', 'T' : '*'}
    return '\\textsuperscript{' + ' '.join(mark_map[m] for m in marks) + '}'

def write_latex():
  '''Generate Latex table from the results dictionary'''
  
  total_count = 0
  to_count = {var : 0 for var in VARIANTS}

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
          ' & ' + b.description + footnotes(b.source) +\
          ' & ' + result.num_procs + render_marks(b.marks) + \
          ' & ' + result.code_size + \
          ' & ' + format_ratio(float(result.code_size), float(result.spec_size)) + \
          ' & ' + format_time(result.time) + \
          ' & ' + format_time(result.variant_times['dfs']) + \
          ' & ' + format_time(result.variant_times['bfs']) + \
          ' & ' + format_time(result.variant_times['memo']) + ' \\\\'

          # ' & ' + result.total_goals + \
          # ' & ' + result.backtracked + \
          # ' & ' + result.variant_total_goals['dfs'] + \
          # ' & ' + result.variant_backtracked['dfs'] + \
          # ' & ' + result.variant_total_goals['bfs'] + \
          # ' & ' + result.variant_backtracked['bfs'] + \
          # ' & ' + result.variant_total_goals['memo'] + \
          # ' & ' + result.variant_backtracked['memo'] + ' \\\\'          
          
          
        outfile.write (row)
        outfile.write ('\n')
        
        total_count = total_count + 1
        for var in VARIANTS:
          if result.variant_times[var] < 0.0:
            to_count[var] = to_count[var] + 1 
        
      outfile.write ('\\hline')
      
  # Copy latex file into the paper directory if properly set
  if os.path.isdir(PAPER_DIR):
    shutil.copy(LATEX_FILE, PAPER_DIR)
  else:
    print 'Paper not found in ', PAPER_DIR  
      
  print 'Total:', total_count
  for var in VARIANTS:
    print 'TO', var, to_count[var]
    
def write_latex_old():
  '''Generate Latex table from the results dictionary'''
  
  total_count = 0
  to_count = {var : 0 for var in VARIANTS}

  with open(OLD_LATEX_FILE, 'w') as outfile:
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
          ' & ' + result.code_size + \
          ' & ' + str(b.suslik_code) + \
          ' & ' + format_time(result.time) + \
          ' & ' + format_time(b.suslik_time) + ' \\\\'
          
        outfile.write (row)
        outfile.write ('\n')
        
        total_count = total_count + 1
        
      outfile.write ('\\hline')
      
  # Copy latex file into the paper directory if properly set
  if os.path.isdir(PAPER_DIR):
    shutil.copy(OLD_LATEX_FILE, PAPER_DIR)
  else:
    print 'Paper not found in ', PAPER_DIR  
      
  print 'Total:', total_count
  for var in VARIANTS:
    print 'TO', var, to_count[var]    
  
def generate_variants():
  '''Generate benchmark variants with disables optimizations'''
  
  for group in groups:
    for b in group.benchmarks:
      test = TEST_DIR + b.name
      testFileName = test + '.syn'
      if not os.path.isfile(testFileName):
        print "Test file not found:", testFileName
      else:
        for var in VARIANTS:
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
              f.write('#. this ' + var_option(var) + '\n' + content)
      
def clean_variants():
  '''Remove previously generated benchmark variants'''
  
  for group in groups:
    for b in group.benchmarks:
      test = TEST_DIR + b.name
      for var in VARIANTS:
        varFileName = test + '-' + var + '.syn'
        if os.path.isfile(varFileName):        
          os.remove(varFileName)
        
def cmdline():
    import argparse
    a = argparse.ArgumentParser()
    a.add_argument('--var', action='store_true')
    a.add_argument('--clean', action='store_true')
    return a.parse_args()        

if __name__ == '__main__':
  # init()
  
  cl_opts = cmdline()
  
  results = dict()
  groups = NEW_BENCHMARKS
  
  if cl_opts.var:
    generate_variants()
  elif cl_opts.clean:
    clean_variants()
  else:        
    # Read stats into a dictionary of synthesis results
    read_csv()
    
    # for res in results:
      # print results[res].str()
    
    # Generate Latex table
    write_latex()
    
  # results = dict()
  # groups = OLD_BENCHMARKS
  # read_csv()
  # write_latex_old()
    
    

    