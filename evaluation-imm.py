import sys
from subprocess import call
import os, os.path
import platform
import shutil
import csv
import functools
import operator

###
#
# @author Andreea Costea
# adapted of evaluation.py
#
# Script for evaluation. For changing the evaluation configuration via the application's
# arguments, simply modify METACONFIG and/or CONFIG.
#
# TODO: currently the properties captured from running a benchmark, such as size, AST, #rule, time, etc,
# are fixed and hardcoded, and so are their corresponding the headers. Need to parameterize that too.
#
###

JAVA8        = 'java'                                             # Path to Java8
SUSLIK_JAR   = 'target/scala-2.12/suslik.jar'                     # Path to suslik.jar
TIMEOUT      = '-t=120000'                                        # Timeout option for suslik
TEST_DIR     = 'src/test/resources/immutable-synthesis/paper-benchmarks/'   # Root directory for the tests
CSV_IN       = 'stats.csv'                                        # Intermediate CSV file produced by suslik
RESULTS      = 'evaluation-utils/all_results'                     # Output file with synthesis results
DEFCONFIG    = ('def', '')                                        # Run with default configuration
METACONFIG   = [DEFCONFIG]                                        # Configurations
CONFIG       = [DEFCONFIG]                                        # Configurations


#################
#  PERFORMANCE  #
#################
PATH1        = "old/lseg/"                                         # Along with TEST_DIR gives full path to the benchmarks
METACONFIG1  = [ DEFCONFIG ]                                       # Meta Configurations
CONFIG1      = [ ('imm', '--imm true'), ('mut', '--imm false') ]   # Configurations
STATS1       = 'evaluation-utils/all_stats1.csv'                   # Output file with all the stats
RESULTS1     = 'evaluation-utils/all_results1'                     # Output file with synthesis results
LATEX_FILE1  = 'evaluation-utils/table1.tex'                       # Output file for generating a latex table


####################
#  ROBUSTNESS  (U) #
####################
PATH2        = "robustness/"                                       # Along with TEST_DIR gives full path to the benchmarks
METACONFIG2  = [ ('imm', '--imm true --flag9 true'), ('mut', '--imm false --flag9 true') ]   # Meta Configurations
CONFIG2      = [#('Default',''),                                    # Configurations
                ('Rank(D)','--flag2 true'),
                # ('Size(A)','--flag3 true'),
                # ('Size(D)','--flag4 true'),
                # # ('Cost(A)','--flag5 true'),
                # # ('Cost(D)','--flag6 true'),
                # ('Alph(A)','--flag7 true'),
                # ('Alph(D)','--flag8 true')
               ]
STATS2       = 'evaluation-utils/all_stats2.csv'                   # Output file with all the stats
RESULTS2     = 'evaluation-utils/all_results2'                     # Output file with synthesis results
LATEX_FILE2  = 'evaluation-utils/table2.tex'                       # Output file for generating a latex table

####################
#  ROBUSTNESS (S)  #
####################
PATH3        = "robustness/"                                       # Along with TEST_DIR gives full path to the benchmarks
METACONFIG3  = [ ('imm', '--imm true --flag10 true'), ('mut', '--imm false --flag10 true') ]   # Meta Configurations
CONFIG3      = [('Default',''),                                    # Configurations
                ('WR1','--flag11 true'),
                # ('U1','--flag14 true'),
              #   ('U2','--flag15 true'),
              #   ('U3','--flag16 true'),
              #   ('WR2','--flag12 true'),
              #   ('WR3','--flag13 true'),
              ]
STATS3       = 'evaluation-utils/all_stats3.csv'                   # Output file with all the stats
STATS4       = 'evaluation-utils/all_stats4.csv'                   # compact stats for the plot
RESULTS3     = 'evaluation-utils/all_results3'                     # Output file with synthesis results
LATEX_FILE3  = 'evaluation-utils/table3.tex'                       # Output file for generating a latex table
SPEC_VAR     = 3

######################
#  ROBUSTNESS (U+S)  #
######################
PATH5        = "robustness/"                                       # Along with TEST_DIR gives full path to the benchmarks
METACONFIG5  = [ ('imm', '--imm true --flag10 true --flag9 true'),
                 ('mut', '--imm false --flag10 true --flag9 true')
               ]                                                   # Meta Configurations
CONFIG5      = [ (a[0] + '-' + b[0], a[1] + ' ' + b[1]) for a in CONFIG3 for b in CONFIG2]
STATS5       = 'evaluation-utils/all_stats5.csv'                   # Output file with all the stats
RESULTS5     = 'evaluation-utils/all_results5'                     # Output file with synthesis results
LATEX_FILE5  = 'evaluation-utils/table5.tex'                       # Output file for generating a latex table
SPEC_VAR     = 3

###################################################################


class SynthesisResult:
  def __init__(self, name, time, spec_size, code_size, backtracking, rules):
    self.name         = name                 # Benchmark name
    self.time         = float(time)          # Synthesis time (seconds)
    self.spec_size    = spec_size            # Cumulative specification size (in AST nodes)
    self.code_size    = code_size            # Cumulative synthesized code size (in AST nodes)
    self.backtracking = backtracking         # The number of times the synthesizer backtracked
    self.rules        = rules                # The number of rules applied by the synthesizer


  def __str__(self):
    return '{0:0.2f}'.format(self.time) + ', ' + self.spec_size + ', ' + self.code_size + ', ' + self.backtracking + ', ' + self.rules


###################################################################


class Benchmark:
  def __init__(self, name, description, categ):
    self.name        = name         # Test file name
    self.description = description  # Description (in the table)
    self.categ       = categ        # category
    self.res         = None         # the result will be an object of class SynthesisResult

  def __str__(self):
    return self.name + ': ' + self.description + ' with results: ' + self.res

  def run_benchmark(self, file, args, results_file):
    '''Runs single benchmark/file'''
    self.res = None
    fargs = list(filter(None, args))
    with open(results_file, "at") as outfile:
      print ('Running ' + file + ' ' + (' '.join(fargs)))
      call([JAVA8, '-jar', SUSLIK_JAR, file, TIMEOUT] + fargs, stdout=outfile)
      self.res = read_csv()
      return self.res # returns a SynthesisResult object


###################################################################


class BenchmarkGroup:
  def __init__(self, name, benchmarks):
    self.name       = name          # Id
    self.benchmarks = benchmarks    # List of benchmarks in this group

  def __str__(self):
    return self.name + ': ' +  ('\n'.join([self.res[b.name] for b in self.benchmarks]))

  # returns a dict of type string -> (SynthesisResult object) which maps
  # the name of each benchmark to the result of running the respective benchmark
  def run_group(self, results_file, args = []):
    '''Runs all the benchmarks in one group'''
    res = dict()
    for b in self.benchmarks:
      test = TEST_DIR + b.name
      testFileName = test + '.syn'
      if not os.path.isfile(testFileName):
        print ("Test file not found:", testFileName)
      else:
        res[b.name] = b.run_benchmark(testFileName, args, results_file)
    return res


###################################################################


class Config:
  def __init__(self, groups, conf = DEFCONFIG):
    self.name    = conf[0]              # Config ID
    self.args    = conf[1].split(' ')   # Config arguments
    self.groups  = groups               # Benchmarks Groups
    self.res     = dict()               # string -> (string-> (SynthesisResult object)): maps the name of each benchmark
                                        # group to the result of running the benchmarks in the respective group

  def __str__(self):
    return self.name + ': ' +  ('\n'.join([self.res[group.name] for group in self.groups]))

  def run_config(self, meta_args, results_file = RESULTS):
    '''Runs all the groups with one configuration'''
    print ('>>>', self.name)
    for group in self.groups:
      self.res[group.name] = group.run_group(results_file, meta_args + self.args) # a map from filename to result
    return self.res  # a map from groups to result


###################################################################


class MetaConfig:
  def __init__(self, configs, metaconf = DEFCONFIG):
    self.name    = metaconf[0]              # MetaConfig ID
    self.args    = metaconf[1].split(' ')   # MetaConfig arguments
    self.configs = configs                  # All the configs which are benchmarked
    self.res     = dict()                   # string -> (string -> (string-> (SynthesisResult object)))
                                            # maps the name of the metaconfig to the result of running the other configs

  def __str__(self):
    return self.name + ': ' + ('\n'.join([self.res[conf[0]] for conf in self.configs]))

  def run_metaconfig(self, groups, results_file = RESULTS):
    '''Runs all the configs assuming the current meta-configuration'''
    print ('***********')
    print ('**', self.name)
    print ('***********')
    for conf in self.configs:
      cnf = Config(groups, conf)
      res_conf  = cnf.run_config(self.args, results_file)
      self.res[conf[0]] = res_conf
    return self.res  # a dictionary from group to result of running the whole group


###################################################################

##########
## misc ##
##########

def foldl(func, acc, xs):
  return functools.reduce(func, xs, acc)

##########

def evaluate(metaconfigs, configs, groups, results_file):
  '''Test all the configurations defined in METACONFIG + CONFIG '''
  results = dict()
  for metaconf in metaconfigs:
      cnf = MetaConfig(configs, metaconf)
      results[metaconf[0]] = cnf.run_metaconfig(groups, results_file)
  return results


def evaluate_n_times(n, metaconfigs, configs, groups, results_file):
  res_lst = []
  for i in range(n):
    groups0 = groups.copy()
    if os.path.isfile(results_file):
      os.remove(results_file)
    res_lst.append(evaluate(metaconfigs, configs, groups0, results_file))

  results = res_lst[0].copy()

  # compute mean result
  for group in groups:
    for b in group.benchmarks:
      for meta in metaconfigs:
        for conf in configs:

          try:
            lst = [int(res_lst[i][meta[0]][conf[0]][group.name][b.name].code_size,10) for i in range(n)]
            results[meta[0]][conf[0]][group.name][b.name].code_size = int(foldl(operator.add, 0, lst) / n)
          except TypeError:
            results[meta[0]][conf[0]][group.name][b.name].code_size = 0

          try:
            lst = [int(res_lst[i][meta[0]][conf[0]][group.name][b.name].spec_size,10) for i in range(n)]
            results[meta[0]][conf[0]][group.name][b.name].spec_size = int(foldl(operator.add, 0, lst) / n)
          except TypeError:
            results[meta[0]][conf[0]][group.name][b.name].spec_size = 0

          try:
            lst = [float(res_lst[i][meta[0]][conf[0]][group.name][b.name].time) for i in range(n)]
            results[meta[0]][conf[0]][group.name][b.name].time = foldl(operator.add, 0, lst) / n
          except TypeError:
            results[meta[0]][conf[0]][group.name][b.name].time = 0

          try:
            lst = [int(res_lst[i][meta[0]][conf[0]][group.name][b.name].backtracking,10) for i in range(n)]
            results[meta[0]][conf[0]][group.name][b.name].backtracking = int(foldl(operator.add, 0, lst) / n)
          except TypeError:
            results[meta[0]][conf[0]][group.name][b.name].backtracking = 0

          try:
            lst = [int(res_lst[i][meta[0]][conf[0]][group.name][b.name].rules,10) for i in range(n)]
            results[meta[0]][conf[0]][group.name][b.name].rules = int(foldl(operator.add, 0, lst) / n)
          except TypeError:
            results[meta[0]][conf[0]][group.name][b.name].rules = 0

  return results

###################################################################

ALL_BENCHMARKS = [
#   BenchmarkGroup("Integers",  [
#     Benchmark(PATH2 + 'ints/swap', 'swap two'),
#     Benchmark(PATH2 + 'ints/min2', 'min of two'),
#     ]),
   BenchmarkGroup("Linked List", [
     Benchmark(PATH2 + 'sll-bounds/sll-len', 'length'),
     Benchmark(PATH2 + 'sll-bounds/sll-max', 'max'),
     Benchmark(PATH2 + 'sll-bounds/sll-min', 'min'),
     Benchmark(PATH2 + 'sll/sll-singleton', 'singleton'),
     Benchmark(PATH2 + 'sll/sll-free', 'dispose'),
     Benchmark(PATH2 + 'sll/sll-init', 'init'),
     Benchmark(PATH2 + 'sll/sll-copy', 'lcopy-val'),
     Benchmark(PATH2 + 'sll/sll-copy-N', 'lcopy-len'),
     Benchmark(PATH2 + 'sll/sll-copy-NS', 'lcopy-all',),
     Benchmark(PATH2 + 'sll/sll-append', 'append'),
     Benchmark(PATH2 + 'sll/sll-delete-all', 'delete'),
     ]),
   BenchmarkGroup("Sorted list", [
     Benchmark(PATH2 + 'srtl/srtl-prepend', 'prepend'),
     Benchmark(PATH2 + 'srtl/srtl-insert-S', 'insert-val'),
     Benchmark(PATH2 + 'srtl/srtl-insert-N', 'insert-len'),
     Benchmark(PATH2 + 'srtl/srtl-insert-NS', 'insert-all'),
     Benchmark(PATH2 + 'srtl/insertion-sort-S', 'ins-sort-val'),
     Benchmark(PATH2 + 'srtl/insertion-sort-N', 'ins-sort-len'),
     Benchmark(PATH2 + 'srtl/insertion-sort-NS', 'ins-sort-all'),
     ]),
    BenchmarkGroup("Tree", [
     Benchmark(PATH2 + 'tree/tree-size-N', 'tsize-len'),
     Benchmark(PATH2 + 'tree/tree-size-NS', 'tsize-all'),
     Benchmark(PATH2 + 'tree/tree-size-N-unique-ptr', 'tsize-ptr-len'),
     Benchmark(PATH2 + 'tree/tree-size-NS-unique-ptr', 'tsize-ptr-all'),
     # Benchmark(PATH2 + 'tree/tree-free', 'dispose'),
     # Benchmark(PATH2 + 'tree/tree-morph', 'morph'),
     Benchmark(PATH2 + 'tree/tree-copy-S', 'tcopy-val'),
     Benchmark(PATH2 + 'tree/tree-copy-N', 'tcopy-len'),
     Benchmark(PATH2 + 'tree/tree-copy-NS', 'tcopy-all'),
     Benchmark(PATH2 + 'tree/tree-copy-S-unique-ptr', 'tcopy-ptr-val'),
     Benchmark(PATH2 + 'tree/tree-copy-N-unique-ptr', 'tcopy-ptr-len'),
     Benchmark(PATH2 + 'tree/tree-copy-NS-unique-ptr', 'tcopy-ptr-all'),
#     Benchmark(PATH2 + 'tree/tree-flatten-S', 'flatten-app'),
#      Benchmark(PATH2 + 'tree/tree-flatten-acc-S', 'flatten-acc'),
     ]),
# #    BenchmarkGroup("BST", [
#      Benchmark(PATH2 + 'bst/bst-insert', 'insert'),
#      Benchmark(PATH2 + 'bst/bst-left-rotate', 'rotate left'),
#      Benchmark(PATH2 + 'bst/bst-right-rotate', 'rotate right'),
#      ]),
  ]

ROBUSTNESS = ALL_BENCHMARKS.copy()

def read_csv():
  '''Read stats file into the results dictionary'''
  with open(CSV_IN, 'rt') as csvfile:
    d = csv.excel
    d.skipinitialspace = True
    statsReader = csv.DictReader(csvfile, dialect = d)
    row = next(statsReader) #assumes that the csv contains stats about one single file
    # The structure below is dependent on suslik's csv output
    name         = row['Name']
    time         = float(row['Time'])/1000
    spec_size    = row['Spec Size']
    code_size    = row['Code Size']
    backtracking = row['Backtrackings']
    rules        = row['Applications']
    syn_res = refine_result(name, time, spec_size, code_size, backtracking, rules)
    return syn_res

def refine_result(name, time, spec_size, code_size, backtracking, rules, variant = 'all'):
  timeOrTO = -1.0 if code_size == 'FAIL' else time
  syn_res  = SynthesisResult(name, timeOrTO, spec_size, code_size, backtracking, rules)
  return syn_res

def format_time(t):
  if t < 0:   return '-'
  if t < 0.1: return '<0.1'
  else:       return '{0:0.1f}'.format(t)


  #################
  #  PERFORMANCE  #
  #################

def write_stats1(metaconfigs, configs, groups, results,stats_file):
  '''Write stats from dictionary into a file'''
  with open(stats_file, 'wt') as stats:
    headings     = ['Code','Spec','Time','Backtrackings','Rules']     #configuration dependent headings
    new_headings = dict()
    for header in headings:
       new_headings[header] = {c[0]: (header + '(' + c[0] + ')') for c in configs}  # creates a header for each conf
    complete_headings = 'Group, Name,' +\
                        ( ','.join([ (",".join([new_headings[header][c[0]] for c in configs])) for header in headings] ))
    stats.write(complete_headings + '\n')

    for group in groups:
      for b in group.benchmarks:
        for meta in metaconfigs:
          #print ((results[meta[0]][configs[0][0]][group.name][b.name].rules))
          row = \
                group.name +\
                ',' + b.description +\
                ',' + (','.join([str(results[meta[0]][conf[0]][group.name][b.name].code_size) for conf in configs])) + \
                ',' + (','.join([str(results[meta[0]][conf[0]][group.name][b.name].spec_size) for conf in configs])) + \
                ',' + (','.join([format_time(results[meta[0]][conf[0]][group.name][b.name].time) for conf in configs])) + \
                ',' + (','.join([str(results[meta[0]][conf[0]][group.name][b.name].backtracking) for conf in configs])) + \
                ',' + (','.join([(str(results[meta[0]][conf[0]][group.name][b.name].rules)) for conf in configs])) +\
                '\n'
          print (row + "   ")
          stats.write(row)

# Assumptions:
#  1. each entry in the csv file starts with the group name, followed by the benchmark description

def read_csv_all(stats_file, performance):
  # saves the results from the stast_file (csv) into
  # a nested dictionary: group -> (benchmark -> [values list])
  groups = dict()
  with open(stats_file, 'rt') as csvfile:
    reader = csv.reader(csvfile)
    for row in reader:
      if not(reader.line_num == 1):
        if not (row[0] in groups):
          groups[row[0]] = dict() #(benchmark -> [values list])
        if not (row[1] in groups[row[0]]):
          groups[row[0]][row[1]] = []

        if performance: skips = [4,5] #skips the specs columns for the performance table
        else: skips = []

        values = []
        for col in range(2,len(row)):
          if col in skips:
            continue
          values.append(row[col])
        groups[row[0]][row[1]].append(values)
  return groups


# Assumptions:
#  1. the `results` parameter is a dictionary whose keys are group names.

def write_stats1_tex(configs, results, latex_file):
    '''Write stats from stats_file into a TEX file'''
    # with open(stats_file, 'wt') as stats:
    with open(latex_file, 'wt') as tex:
        headings = ['AST size','Time','\\#Backtr.','\\#Rules']     #configuration dependent headings
        len_cols = 2 + len(headings) * len(configs) + 1
        hhline  = '\\hhline{' + ('=' * len_cols) + '}'
        prefix  = '\\begin{tabular}{@{} c | c | ' +   ("|".join([ (' c ' * len(configs)) for h in headings])) + ' | c  @{}}\n'
        postfix = '\\\\ \n ' + hhline + ' \n  \\end{tabular}'
        complete_headings = '\\multirow{2}{*}{\\head{Group}}' + \
                            '\n &' + '\\multirow{2}{*}{\\head{Description}}' + \
                            '\n &' + ('\n & '.join([ ('\\multicolumn{2}{c|}{ \\head{' + h + '} } ') for h in headings])) + \
                            '\n &' + '{\\head{Stronger}}' + \
                            '\n \\\\' + \
                            '\n &' + '' + \
                            '\n &' + ('&'.join(['&'.join([c[0] for c in configs])] * len(headings))) + \
                            '\n &' + '{\\head{Guarantees}}' + \
                            '\n \\\\ ' + \
                            '\n  ' + hhline + '  \n'
        entries = []
        sep =''
        for grp in sorted(results):
            if (len(entries) > 0):
                sep = '\n \\hline \n'
            benchmarks = results[grp]
            ln_grp = 0
            for file in benchmarks:
                ln_grp  += len(benchmarks[file])
            entry1_grp  = sep + '\\multirow{' + str(ln_grp) + '}{*}{' + grp + '} '
            for file in sorted(benchmarks):
                ln_file = len(benchmarks[file])
                entry1_file = '\\multirow{' + str(ln_file) + '}{*}{' + file + '} '
                benchmark = benchmarks[file]
                entry =          entry1_grp   +\
                         ' & ' + entry1_file  +\
                         ' & ' + (' & '.join([ val for val in benchmark[0] ]))
                entries.append(entry)
                entry1_grp    = ''
                for lst in benchmark[1:ln_file]:
                    entries.append(' &  & & ' + (' & '.join([ val for val in lst ])))
        entries_final = '\n \\\\ \n '.join([entry for entry in entries])
        tex.write(prefix + complete_headings + entries_final + postfix)


  #################
  #  ROBUSTNESS   #
  #################

def write_stats2(metaconfigs, configs, groups, results,stats_file):
  '''Write stats from dictionary into a file'''
  with open(stats_file, 'wt') as stats:
    complete_headings = 'Group, Name, Assesed Property, Meta Config, ' + ( ','.join([ (",".join([c[0] for c in configs]))] ))
    stats.write(complete_headings + '\n')

    for group in groups:
      for b in group.benchmarks:
        # AST size
        for meta in metaconfigs:
            row1 = \
                group.name +\
                ',' + b.description +\
                ',' + 'AST size' +\
                ',' + meta[0] +\
                ',' + (','.join([str(results[meta[0]][conf[0]][group.name][b.name].code_size) for conf in configs])) + \
                '\n'
            print (row1)
            stats.write(row1)
        # Spurious writes (for now needs to be manually added)
        # for meta in metaconfigs:
        #     row2 = \
        #         group.name +\
        #         ',' + b.description +\
        #         ',' + 'SW' + \
        #         ',' + meta[0] + \
        #         ',' + (','.join(['' for conf in configs])) + \
        #         '\n'
        #     print (row2)
        #     stats.write(row2)
        # # the number of backtracking
        # for meta in metaconfigs:
        #     row3 = \
        #         group.name +\
        #         ',' + b.description +\
        #         ',' + '\\#backtr' + \
        #         ',' + meta[0] + \
        #         ',' + (','.join([str(results[meta[0]][conf[0]][group.name][b.name].backtracking) for conf in configs])) + \
        #         '\n'
        #     print (row3)
        #     stats.write(row3)
        # the number of rules fired
        for meta in metaconfigs:
            row4 = \
                group.name +\
                ',' + b.description +\
                ',' + '\\#rules' + \
                ',' + meta[0] + \
                ',' + (','.join([str(results[meta[0]][conf[0]][group.name][b.name].rules) for conf in configs])) + \
                '\n'
            print (row4)
            stats.write(row4)

def write_stats2_tex(metaconfig, configs, results, latex_file):
    '''Write stats from stats_file into a TEX file'''
    # with open(stats_file, 'wt') as stats:
    with open(latex_file, 'wt') as tex:
        prefix  = '\\begin{tabular}{@{} c | c |  c | c |' +   (' '.join([ ' c ' for c in configs])) + '   @{}}\n'
        len_cols = 4 + len(configs)
        hhline  = '\\hhline{' + ('=' * len_cols) + '}'
        postfix = '\\\\ \n ' + hhline + '  \n  \\end{tabular}'
        complete_headings = '{\\head{Group}}' + \
                            '\n &' + '{\\head{Description}}' + \
                            '\n &' + '{\\head{Property}}' + \
                            '\n &' + '{\\head{imm/mut}}' + \
                            '\n &' + ( '&'.join([('\\head{' + c[0] + '}') for c in configs])) + \
                            '\n \\\\' +\
                            hhline + ' \n'

        sep_grp     = '\\hline'
        sep_file    = '\\cline{2 - ' + str(len_cols)  + '} \n' # file separator
        sep_prop    = '\\cline{3 - ' + str(len_cols)  + '} \n' # property separator
        sep_line    = '\n \\\\ \n '

        entries     = []
        pre_grp     = ''
        pre_prop    = sep_prop
        line_sep    = sep_line

        for grp in sorted(results):
            if (len(entries) > 0):
                pre_grp  = '\n ' + sep_grp + ' \n'  #group separator
            benchmarks = results[grp]
            entry1_grp = ''
            ln_grp = 0
            for file in benchmarks:
                ln_grp  += len(benchmarks[file])
            entry1_grp  = pre_grp + '\\multirow{' + str(ln_grp) + '}{*}{' + grp + '} '
            for file in benchmarks:
                pre_file    = sep_file
                if entry1_grp != '': pre_file = ''
                ln_file     = len(benchmarks[file])
                entry1_file = '\\multirow{' + str(ln_file) + '}{*}{' + file + '} '
                benchmark   = benchmarks[file]

                #first entry per file
                values1     = benchmark[0]
                entry1      =    pre_file +\
                                 entry1_grp   + \
                                 ' & ' + entry1_file  + \
                                 ' & ' + '\\multirow{2}{*}{' + values1[0] + '} & '+\
                                 (' & '.join([ val for val in values1[1:len(values1)] ]))
                entries.append(entry1)
                entry1_grp  = ''  # reset grp entry to allow for multirow group

                #second entry per file
                values2     = benchmark[1]
                entries.append( ' &  &  & ' + (' & '.join([ val for val in values2[1:len(benchmark[1])] ])))

                # subsequent entries for file `benchmark` paired
                # to allow cline separation and multirow for each property
                values      = benchmark[2:ln_file]
                for lst1,lst2 in zip(values[::2],values[1::2]):
                    ln_fline = len(benchmark[0])
                    property_entr = pre_prop +\
                                    ' &  & ' + '\\multirow{2}{*}{' + lst1[0] + '} & '+\
                                    (' & '.join([ val for val in lst1[1:ln_fline] ])) +\
                                    line_sep +\
                                    ( ' &  & & ' + (' & '.join([ val for val in lst2[1:ln_fline] ])))
                    entries.append(property_entr)
        entries_final = line_sep.join([entry for entry in entries])
        tex.write(prefix + complete_headings + entries_final + postfix)


def write_stats3(metaconfigs, configs, groups, results,stats_file):
  '''Write stats from dictionary into a file'''
  with open(stats_file, 'wt') as stats:
    complete_headings = 'Group, Name, Assesed Property, Meta Config, ' +\
                        (",".join([c[0] for c in configs] * SPEC_VAR))
    stats.write(complete_headings + '\n')

    # Init
    robustness_res = dict()
    for group in groups:
      robustness_res[group] = dict()
      for meta in metaconfigs:
        robustness_res[group][meta] = dict()
        for b in group.benchmarks:
          robustness_res[group][meta][b.categ] = dict()
          robustness_res[group][meta][b.categ]['AST size'] = []
          robustness_res[group][meta][b.categ]['rules']    = []

    # Populate
    categ = dict()
    for group in groups:
      for meta in metaconfigs:
        for b in group.benchmarks:
          robustness_res[group][meta][b.categ]['AST size'] += ((results[meta[0]][conf[0]][group.name][b.name].code_size) for conf in configs)
          robustness_res[group][meta][b.categ]['rules'] += ((results[meta[0]][conf[0]][group.name][b.name].rules) for conf in configs)
          categ[b.categ] = [b.categ]

    categories = categ.keys()
    for group in groups:
      for b in categories:
        for meta in metaconfigs:
            row1 = \
                group.name +\
                ',' + b[0] +\
                ',' + 'AST size' +\
                ',' + meta[0] +\
                ',' + (','.join(str(x) for x in (robustness_res[group][meta][b]['AST size'])))+ \
                '\n'
            stats.write(row1)
        for meta in metaconfigs:
            row2 = \
                group.name +\
                ',' + b[0] +\
                ',' + 'rules' +\
                ',' + meta[0] +\
                ',' + (','.join(str(x) for x in (robustness_res[group][meta][b]['rules'])))+ \
                '\n'
            stats.write(row2)


def cmdline():
  import argparse
  a = argparse.ArgumentParser()
  a.add_argument('--tiny', action='store_true')
  a.add_argument('--stats',action='store_true')
  a.add_argument('--robustnessUS',action='store_true')   #disables the robustness eval
  a.add_argument('--robustnessU',action='store_true')    #disables the robustness eval
  a.add_argument('--robustnessS',action='store_true')    #disables the robustness eval
  a.add_argument('--performance',action='store_true')    #disables the performance eval
  a.add_argument('--latex',action='store_true')          #generates the latex tables
  a.add_argument('--n', type=int, default=1)             #every returned value is the mean of n runs
  return a.parse_args()

if __name__ == '__main__':
  cl_opts = cmdline()
  repetitions = cl_opts.n


  #################
  #  PERFORMANCE  #
  #################

  if not(cl_opts.performance):
      results1 = evaluate_n_times(repetitions, METACONFIG1, CONFIG1, ALL_BENCHMARKS, RESULTS1)
      write_stats1(METACONFIG1, CONFIG1, ALL_BENCHMARKS, results1, STATS1)

  if (cl_opts.latex):
    res = read_csv_all(STATS1,True)
    write_stats1_tex(CONFIG1,res,LATEX_FILE1)

  ####################
  #  ROBUSTNESS (U)  #
  ####################

  if os.path.isfile(RESULTS2):
    os.remove(RESULTS2)

  if not(cl_opts.robustnessU):
      results2 = evaluate_n_times(repetitions, METACONFIG2, CONFIG2, ROBUSTNESS, RESULTS2)
      write_stats2(METACONFIG2, CONFIG2, ROBUSTNESS, results2, STATS2)

  if (cl_opts.latex):
    res = read_csv_all(STATS2,False)
    write_stats2_tex(METACONFIG2,CONFIG2,res,LATEX_FILE2)

  ######################
  #  ROBUSTNESS (U+S)  #
  ######################

  if os.path.isfile(RESULTS5):
    os.remove(RESULTS5)

  if not(cl_opts.robustnessUS):
      results5 = evaluate_n_times(repetitions, METACONFIG5, CONFIG5, ROBUSTNESS, RESULTS5)
      write_stats2(METACONFIG5, CONFIG5, ROBUSTNESS, results5, STATS5)


  ####################
  #  ROBUSTNESS (S)  #
  ####################

  if os.path.isfile(RESULTS3):
    os.remove(RESULTS3)

  if not(cl_opts.robustnessS):
      results3 = evaluate_n_times(repetitions, METACONFIG3, CONFIG3, ROBUSTNESS, RESULTS3)
      write_stats2(METACONFIG3, CONFIG3, ROBUSTNESS, results3, STATS3)
      # write_stats3(METACONFIG3, CONFIG3, ROBUSTNESS, results3, STATS4)

  if (cl_opts.latex):
    res3 = read_csv_all(STATS3,False)
    write_stats2_tex(METACONFIG3,CONFIG3,res3,LATEX_FILE3)
