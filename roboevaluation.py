import copy
from subprocess import call
import os, os.path
import csv
import functools
import operator
import random

###
#
# @author Andreea Costea and Yutaka Nagashima
# adapted of evaluation.py
#
# Script for evaluation. For changing the evaluation configuration via the application's
# arguments, simply modify METACONFIG and/or CONFIG.
#
# TODO: currently the properties captured from running a benchmark, such as size, AST, #rule, time, etc,
# are fixed and hardcoded, and so are their corresponding headers. Need to parameterize that too.
#
#
# Running the performance eval (averages 3 runs of the benchmarks, can add --latex for dumping everything in a tex table):
#    `python3 robo-evaluation.py --performance --n 3`
#    csv output: robo-evaluation-utils/stats-performance.csv
#    tex output: robo-evaluation-utils/table1.tex
#
###

#################
#    DEFAULT    #
#################
JAVA8        = 'java'                                             # Path to Java8
SUSLIK_JAR   = 'target/scala-2.12/suslik.jar'                     # Path to suslik.jar
TIMEOUT      = '-t=3000'                                          # Timeout option for suslik
TEST_DIR     = 'src/test/resources/synthesis/all-benchmarks/'     # Root directory for the tests
CSV_IN       = 'stats.csv'                                        # Intermediate CSV file produced by suslik
CSV_TEMP     = 'stats-temp.csv'                                   # Intermediate CSV file produced by suslik
EVAL_FOLDER  = 'robo-evaluation-utils'                            # the folder with most of the eval utils and stats
RESULTS      = EVAL_FOLDER + '/all_results'                       # Output file with synthesis results
DEFCONFIG    = ('def', '')                                        # Run with default configuration
METACONFIG   = [DEFCONFIG]                                        # Configurations
CONFIG       = [DEFCONFIG]                                        # Configurations


#################
#  PERFORMANCE  #
#################
PATH1        = ""                                                  # Along with TEST_DIR gives full path to the benchmarks
METACONFIG1  = [ DEFCONFIG ]                                       # Meta Configurations
CONFIG1      = [ ('mut', '') ]                                     # Configurations
STATS1       = EVAL_FOLDER + '/stats-performance.csv'              # Output file with all the statssRESULTS1     = EVAL_FOLDER + '/all_results1'                       # Output file with synthesis results
RESULTS1     = EVAL_FOLDER + '/all_results1'                       # Output file with synthesis results
LATEX_FILE1  = EVAL_FOLDER + '/table1.tex'                         # Output file for generating a latex table

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
  def __init__(self, name, description, is_for_training):
    self.name        = name         # Test file name
    self.description = description  # Description (in the table)
    self.is_for_training = is_for_training # 0 for validation, 1 for evolution (training)
    self.res         = None         # the result will be an object of class SynthesisResult

  def __str__(self):
    return self.name + ': ' + self.description + ' with results: ' + self.res

  def run_benchmark(self, file, args, results_file, csv_in, csv_out, evolution=False, group_id=0, generation_id=0,
                    individual_id=0):
    '''Runs single benchmark/file'''

    self.res = None

    fargs = list(filter(None, args))

    if evolution:
        args_evolution = ['--evolutionary', 'True', '--groupID', str(group_id), '--generationID', str(generation_id),
                          '--individualID', str(individual_id)]
    else:
        args_evolution = []

    with open(results_file, "at") as outfile:
      print ('Running ' + file + ' ' + (' '.join(fargs)))
      call([JAVA8, '-jar', SUSLIK_JAR, file, TIMEOUT] + fargs + args_evolution, stdout=outfile)
      self.res = read_csv(csv_in)
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
  def run_group(self, results_file, csv_in, csv_out, args = [], evolution=False, group_id=0, generation_id=0,
                individual_id=0):
    '''Runs all the benchmarks in one group'''
    res = dict()
    for b in self.benchmarks:
      test = TEST_DIR + b.name
      testFileName = test + '.syn'
      if not os.path.isfile(testFileName):
        print ("Test file not found:", testFileName)
      else:
        res[b.name] = b.run_benchmark(testFileName, args, results_file,csv_in, csv_out, evolution, group_id,
                                      generation_id, individual_id)
    return res


def get_benchmark_group_for_training(group:BenchmarkGroup):
    benchmarks_for_training = []
    for benchmark in group.benchmarks:
        if benchmark.is_for_training:
            print(benchmark.name)
            benchmarks_for_training.append(copy.deepcopy(benchmark))
    return BenchmarkGroup(group.name, benchmarks_for_training)

def get_benchmark_group_for_validation(group:BenchmarkGroup):
    benchmarks_for_validation = []
    for benchmark in group.benchmarks:
        if not benchmark.is_for_training:
            print(benchmark.name)
            benchmarks_for_validation.append(copy.deepcopy(benchmark))
    return BenchmarkGroup(group.name, benchmarks_for_validation)

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

  def run_config(self, meta_args, csv_in, csv_out, results_file = RESULTS, evolution=False, group_id=0, generation_id=0,
                 individual_id=0):
    '''Runs all the groups with one configuration'''
    print ('>>>', self.name)
    for group in self.groups:
      self.res[group.name] = group.run_group(results_file, csv_in, csv_out, meta_args + self.args, evolution,
                                             group_id, generation_id, individual_id) # a map from filename to result
    with open(csv_out, "at") as tempfile:
      tempfile.write('>>>' + self.name + '\n')
      for group in self.groups:
        for b in group.benchmarks:
          row = \
                group.name +\
                ',' + b.description +\
                ',' + self.res[group.name][b.name].code_size + \
                ',' + self.res[group.name][b.name].rules +\
                '\n'
          tempfile.write(row)
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

  def run_metaconfig(self, groups, csv_in, csv_out, results_file = RESULTS, evolution=False, group_id=0,
                     generation_id=0, individual_id=0):
    '''Runs all the configs assuming the current meta-configuration'''
    print ('***********')
    print ('**', self.name)
    print ('***********')
    with open(csv_out, "at") as tempfile:
      tempfile.write('****' + self.name + '\n')
    for conf in self.configs:
      cnf = Config(groups, conf)
      res_conf  = cnf.run_config(self.args, csv_in, csv_out, results_file, evolution, group_id, generation_id,
                                 individual_id)
      self.res[conf[0]] = res_conf
    return self.res  # a dictionary from group to result of running the whole group


###################################################################

##########
## misc ##
##########

def foldl(func, acc, xs):
  return functools.reduce(func, xs, acc)

##########

def evaluate(metaconfigs, configs, groups, results_file, csv_in, csv_out, evolution=False,
             group_id=0, generation_id=0, individual_id=0):
  '''Test all the configurations defined in METACONFIG + CONFIG '''
  results = dict()
  for metaconf in metaconfigs:
      cnf = MetaConfig(configs, metaconf)
      results[metaconf[0]] = cnf.run_metaconfig(groups, csv_in, csv_out, results_file, evolution, group_id,
                                                generation_id, individual_id)
  return results


def evaluate_n_times(n, metaconfigs, configs, groups, results_file, csv_in, csv_out, evolution=False,
                     group_id=0, generation_id=0, individual_id=0):
  res_lst = []
  for i in range(n):
    groups0 = groups.copy()
    if os.path.isfile(results_file):
      os.remove(results_file)
    res_lst.append(evaluate(metaconfigs, configs, groups0, results_file, csv_in, csv_out, evolution, group_id,
                            generation_id, individual_id))

  results = res_lst[0].copy()

  # compute mean result
  for group in groups:
    for b in group.benchmarks:
      for meta in metaconfigs:
        for conf in configs:

          try:
            lst = [int(res_lst[i][meta[0]][conf[0]][group.name][b.name].code_size,10) for i in range(n)]
            results[meta[0]][conf[0]][group.name][b.name].code_size = int(foldl(operator.add, 0, lst) / n)
          except:
            results[meta[0]][conf[0]][group.name][b.name].code_size = 'FAIL'

          try:
            lst = [int(res_lst[i][meta[0]][conf[0]][group.name][b.name].spec_size,10) for i in range(n)]
            results[meta[0]][conf[0]][group.name][b.name].spec_size = int(foldl(operator.add, 0, lst) / n)
          except:
            results[meta[0]][conf[0]][group.name][b.name].spec_size = 'FAIL'

          try:
            lst = [float(res_lst[i][meta[0]][conf[0]][group.name][b.name].time) for i in range(n)]
            results[meta[0]][conf[0]][group.name][b.name].time = foldl(operator.add, 0, lst) / n
          except:
            results[meta[0]][conf[0]][group.name][b.name].time = 'FAIL'

          try:
            lst = [int(res_lst[i][meta[0]][conf[0]][group.name][b.name].backtracking,10) for i in range(n)]
            results[meta[0]][conf[0]][group.name][b.name].backtracking = int(foldl(operator.add, 0, lst) / n)
          except:
            results[meta[0]][conf[0]][group.name][b.name].backtracking = 'FAIL'

          try:
            lst = [int(res_lst[i][meta[0]][conf[0]][group.name][b.name].rules,10) for i in range(n)]
            results[meta[0]][conf[0]][group.name][b.name].rules = int(foldl(operator.add, 0, lst) / n)
          except:
            results[meta[0]][conf[0]][group.name][b.name].rules = 'FAIL'

  return results

PORTION_OF_TRAINING = 0.5
random.seed

def mutBit(i,indpb):
    if random.random() < indpb:
        return not i
    else:
        return i


ALL_BENCHMARKS = [
    BenchmarkGroup("Integers", [
        Benchmark('ints/swap', 'swap two', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('ints/min2', 'min of two', mutBit(0, PORTION_OF_TRAINING)),
    ]),
    BenchmarkGroup("Singly Linked List", [
        Benchmark('sll/len', 'length', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/max', 'max', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/min', 'min', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/singleton', 'singleton', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/free', 'deallocate', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/init', 'initialize', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/copy', 'copy', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/append', 'append', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/delete-all', 'delete', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/free2', 'deallocate two', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/multi-append', 'append three', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/append-copy', 'non-destructive append', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/union', 'union', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/intersect', 'intersection', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/diff', 'difference', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('sll/unique', 'deduplicate', mutBit(0, PORTION_OF_TRAINING)),
    ]),
    BenchmarkGroup("Sorted list", [
        Benchmark('srtl/prepend', 'prepend', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('srtl/insert', 'insert', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('srtl/insertion-sort', 'insertion sort', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('srtl/sort', 'sort', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('srtl/reverse', 'reverse', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('srtl/merge', 'merge', mutBit(0, PORTION_OF_TRAINING)),
    ]),
    BenchmarkGroup("Doubly Linked List", [
        Benchmark('dll/singleton', 'singleton', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('dll/copy', 'copy', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('dll/append', 'append', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('dll/delete-all', 'delete', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('dll/from-sll', 'single to double', mutBit(0, PORTION_OF_TRAINING)),
    ]),
    BenchmarkGroup("List of Lists", [
        Benchmark('multi-list/free', 'deallocate', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('multi-list/flatten', 'flatten', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('multi-list/len', 'length', mutBit(0, PORTION_OF_TRAINING)),
    ]),
    BenchmarkGroup("Binary Tree", [
        Benchmark('tree/size', 'size', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('tree/free', 'deallocate', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('tree/free2', 'deallocate two', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('tree/copy', 'copy', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('tree/flatten-helper', 'flatten w/append', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('tree/flatten-acc', 'flatten w/acc', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('tree/flatten', 'flatten', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('tree/flatten-dll', 'flatten to dll in place', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('tree/flatten-dll-linear', 'flatten to dll w/null', mutBit(0, PORTION_OF_TRAINING)),
    ]),
    BenchmarkGroup("BST", [
        Benchmark('bst/insert', 'insert', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('bst/left-rotate', 'rotate left', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('bst/right-rotate', 'rotate right', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('bst/min', 'find min', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('bst/max', 'find max', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('bst/delete-root', 'delete root', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('bst/list-to-bst', 'from list', mutBit(0, PORTION_OF_TRAINING)),
        Benchmark('bst/to-srtl', 'to sorted list', mutBit(0, PORTION_OF_TRAINING)),
    ]),
     BenchmarkGroup("Rose Tree", [
         Benchmark('rose-tree/free', 'deallocate', mutBit(0, PORTION_OF_TRAINING)),
         Benchmark('rose-tree/flatten', 'flatten', mutBit(0, PORTION_OF_TRAINING)),
         Benchmark('rose-tree/copy', 'copy', mutBit(0, PORTION_OF_TRAINING)),
     ]),
     BenchmarkGroup("Packed Tree", [
         Benchmark('packed/pack', 'pack', mutBit(0, PORTION_OF_TRAINING)),
         Benchmark('packed/unpack', 'unpack', mutBit(0, PORTION_OF_TRAINING)),
     ]),
  ]

TRAINING_DATA = list(map(get_benchmark_group_for_training, ALL_BENCHMARKS))
VALIDATION_DATA = list(map(get_benchmark_group_for_validation, ALL_BENCHMARKS))

###################################################################

def read_csv(csv_in):
  '''Read stats file into the results dictionary'''
  with open(csv_in, 'rt') as csvfile:
    d = csv.excel
    d.skipinitialspace = True
    statsReader = csv.DictReader(csvfile, dialect = d)
    row = next(statsReader) #assumes that the csv contains stats about one single file
    toberemoved = row.keys()
    print(toberemoved)
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

def write_stats1(metaconfigs, configs, groups, results, stats_file):
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

def cmdline():
  import argparse
  a = argparse.ArgumentParser()
  a.add_argument('--performance',action='store_true')        #performance eval
  a.add_argument('--latex',action='store_true')              #generates the latex tables
  a.add_argument('--n', type=int, default=1)                 #every returned value is the mean of n runs
  a.add_argument('--evolutionary',action='store_true')       #genetic algorithm to improve rule ordering
  a.add_argument('--group', type=int,default=0)              #ID of group for genetic algorithm
  a.add_argument('--generation', type=int,default=0)         #ID of generation for genetic algorithm
  a.add_argument('--individual', type=int,default=0)         #ID of individual for genetic algorithm
  return a.parse_args()

if __name__ == '__main__':
  cl_opts = cmdline()
  repetitions = cl_opts.n

  #################
  #  PERFORMANCE  #
  #################

  if (cl_opts.latex):
    res = read_csv_all(STATS1,True)
    write_stats1_tex(CONFIG1,res,LATEX_FILE1)

  if (cl_opts.performance):
      results1 = evaluate_n_times(repetitions, METACONFIG1, CONFIG1, TRAINING_DATA, RESULTS1, CSV_IN, CSV_TEMP,
                                  cl_opts.group, cl_opts.generation, cl_opts.individual)
      write_stats1(METACONFIG1, CONFIG1, TRAINING_DATA, results1, STATS1)
