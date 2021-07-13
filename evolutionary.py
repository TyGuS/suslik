import array
import os
import random
import json
import copy
from subprocess import call

import roboevaluation

import numpy
import pandas

from deap import algorithms
from deap import base
from deap import creator
from deap import tools

PATH_TO_TACTICS = "src/main/scala/org/tygus/suslik/synthesis/tactics/parameters/"
NUMB_OF_ANY_PHASE_RULE = 8
NUMB_OF_PURE_PHASE_RULE = 10
NUMB_OF_SYMBOLIC_EXECUTION_RULE = 6
NUMB_OF_UNFOLDING_PHASE_RULE = 5
NUMB_OF_ANY_PHASE_RULE_OR_SPEC_BASED_RULE = 2
NUMB_OF_SKETCH_HOLE = 3
MAXIMUM_NUMBER_OF_FAILED_SYNTHESIS = 0
MAXIMUM_TOTAL_TIME = 50.0
POPULATION_SIZE = 5
MAXIMUM_NUMBER_OF_GENERATIONS = 30
INDPB = 0.1
NUMB_OF_FEATURES = 7
NUMB_OF_FEATURE_COMBINATION = 2 ** NUMB_OF_FEATURES

class Individual(list):
    """This class describe SuSLik's search strategy for individuals in each population."""

    def __init__(self,
                 population_id,
                 individual_id,
                 rank,
                 nan=10,
                 time=9999999999.0,
                 orders_of_any_phase_rules=None,
                 orders_of_pure_phase_rules=None,
                 orders_of_symbolic_execution_rules=None,
                 orders_of_unfolding_phase_rules=None,
                 orders_of_any_phase_rules_or_spec_based_rules=None,
                 orders_of_sketch_hole=None):
        super().__init__()
        self.population_id = population_id
        self.individual_id = individual_id
        self.rank = rank
        self.nan = nan
        self.time = time

        if orders_of_any_phase_rules is None:
            orders_of_any_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_any_phase_rules.append(random.sample(range(NUMB_OF_ANY_PHASE_RULE), NUMB_OF_ANY_PHASE_RULE))
        print("Number of items in orders_of_any_phase_rules = ", len(orders_of_any_phase_rules))
        self.orders_of_any_phase_rules = orders_of_any_phase_rules

        if orders_of_pure_phase_rules is None:
            orders_of_pure_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_pure_phase_rules.append\
                    (random.sample(range(NUMB_OF_PURE_PHASE_RULE), NUMB_OF_PURE_PHASE_RULE))
        print("Number of items in orders_of_pure_phase_rules = ", len(orders_of_pure_phase_rules))
        self.orders_of_pure_phase_rules = orders_of_pure_phase_rules

        if orders_of_symbolic_execution_rules is None:
            orders_of_symbolic_execution_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_symbolic_execution_rules.append\
                    (random.sample(range(NUMB_OF_SYMBOLIC_EXECUTION_RULE), NUMB_OF_SYMBOLIC_EXECUTION_RULE))
        print("Number of items in orders_of_symbolic_execution_rules = ", len(orders_of_symbolic_execution_rules))
        self.orders_of_symbolic_execution_rules = orders_of_symbolic_execution_rules

        if orders_of_unfolding_phase_rules is None:
            orders_of_unfolding_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_unfolding_phase_rules.append\
                    (random.sample(range(NUMB_OF_UNFOLDING_PHASE_RULE), NUMB_OF_UNFOLDING_PHASE_RULE))
        print("Number of items in orders_of_unfolding_phase_rules = ", len(orders_of_unfolding_phase_rules))
        self.orders_of_unfolding_phase_rules = orders_of_unfolding_phase_rules

        if orders_of_any_phase_rules_or_spec_based_rules is None:
            orders_of_any_phase_rules_or_spec_based_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_any_phase_rules_or_spec_based_rules.append\
                    (random.sample(range(NUMB_OF_ANY_PHASE_RULE_OR_SPEC_BASED_RULE),
                                   NUMB_OF_ANY_PHASE_RULE_OR_SPEC_BASED_RULE))
        print("Number of items in orders_of_unfolding_phase_rules = ", len(orders_of_any_phase_rules_or_spec_based_rules))
        self.orders_of_any_phase_rules_or_spec_based_rules = orders_of_any_phase_rules_or_spec_based_rules

        if orders_of_sketch_hole is None:
            orders_of_sketch_hole = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_sketch_hole.append(random.sample(range(NUMB_OF_SKETCH_HOLE), NUMB_OF_SKETCH_HOLE))
        print("Number of items in orders_of_sketch_hole = ", len(orders_of_sketch_hole))
        self.orders_of_sketch_hole = orders_of_sketch_hole

    def get_individual_id(self):
        return self.individual_id

    def set_individual_id(self, individual_id):
        self.individual_id = individual_id

    def get_population_id(self):
        return self.population_id

    def set_population_id(self, population_id):
        self.population_id = population_id

    def set_rank(self, rank):
        self.rank = rank

    def get_time(self):
        return self.time

    def get_nan(self):
        return self.nan

    def set_time(self, time):
        self.time = time

    def set_nan(self, nan):
        self.nan = nan

    def mutate(self):
        for order_of_any_phase_rules in self.orders_of_any_phase_rules:
            tools.mutShuffleIndexes(order_of_any_phase_rules, indpb=INDPB)
        for order_of_pure_phase_rules in self.orders_of_pure_phase_rules:
            tools.mutShuffleIndexes(order_of_pure_phase_rules, indpb=INDPB)
        for order_of_symbolic_execution_rules in self.orders_of_symbolic_execution_rules:
            tools.mutShuffleIndexes(order_of_symbolic_execution_rules, indpb=INDPB)
        for order_of_unfolding_phase_rules in self.orders_of_unfolding_phase_rules:
            tools.mutShuffleIndexes(order_of_unfolding_phase_rules, indpb=INDPB)
        for order_of_any_phase_rules_or_spec_based_rules in self.orders_of_any_phase_rules_or_spec_based_rules:
            tools.mutShuffleIndexes(order_of_any_phase_rules_or_spec_based_rules, indpb=INDPB)
        for order_of_sketch_hole in self.orders_of_sketch_hole:
            tools.mutShuffleIndexes(order_of_sketch_hole, indpb=INDPB)

    def json_file_path(self):
        json_file_name = "search_parameter" + "_" + str(self.population_id) + "_" + str(self.individual_id) + ".json"
        path = PATH_TO_TACTICS + json_file_name
        return path

    def write_order_json(self):

        json_data_to_write = {
            "numbOfAnyPhaseRules": NUMB_OF_ANY_PHASE_RULE,
            "orders_of_any_phase_rules": self.orders_of_any_phase_rules,
            "orders_of_pure_phase_rules": self.orders_of_pure_phase_rules,
            "orders_of_symbolic_execution_rules": self.orders_of_symbolic_execution_rules,
            "orders_of_unfolding_phase_rules": self.orders_of_unfolding_phase_rules,
            "orders_of_any_phase_rules_or_spec_based_rules": self.orders_of_any_phase_rules_or_spec_based_rules,
            "orders_of_sketch_hole": self.orders_of_sketch_hole
        }

        with open(self.json_file_path(), 'w') as new_json_file_to_write:
            json.dump(json_data_to_write, new_json_file_to_write)

    def csv_path(self):
        path = roboevaluation.EVAL_FOLDER + '/stats-performance_' + str(self.population_id) + '_' + str(
            self.individual_id) + '.csv'
        return path

    def evaluate(self):

        self.write_order_json()

        results1 = roboevaluation.evaluate_n_times(
            1, roboevaluation.METACONFIG1, roboevaluation.CONFIG1, roboevaluation.ALL_BENCHMARKS,
            roboevaluation.RESULTS1, roboevaluation.CSV_IN, roboevaluation.CSV_TEMP, True, self.population_id,
            self.individual_id)

        roboevaluation.write_stats1(roboevaluation.METACONFIG1, roboevaluation.CONFIG1, roboevaluation.ALL_BENCHMARKS,
                                    results1, self.csv_path())

        df = pandas.read_csv(filepath_or_buffer=self.csv_path(), na_values=['FAIL', '-'])

        number_of_nans = int(df['Time(mut)'].isna().sum())
        total_time = df['Time(mut)'].sum()

        self.nan, self.time = (number_of_nans, total_time)

        return number_of_nans, total_time

    def is_not_good_enough(self):
        return (self.nan > MAXIMUM_NUMBER_OF_FAILED_SYNTHESIS) or (self.time > MAXIMUM_TOTAL_TIME)

    # Note that we use the rank of individual in the file name.
    def json_result_file_path(self):
        return "robo-evaluation-utils/result" + "_" + str(self.population_id) + "_" + str(self.rank) \
                         + ".json"

    def json_result(self):
        return {
            "generation_ID": self.population_id,
            "individual_ID": self.individual_id,
            "rank": self.rank,
            "number_of_nan": self.nan,
            "search_time": self.time
            #"orders_of_any_phase_rules": self.orders_of_any_phase_rules,
            #"orders_of_pure_phase_rules": self.orders_of_pure_phase_rules,
            #"orders_of_symbolic_execution_rules": self.orders_of_symbolic_execution_rules,
            #"orders_of_unfolding_phase_rules": self.orders_of_unfolding_phase_rules
        }

    def write_json_result(self):

        with open(self.json_result_file_path(), 'w') as json_result_file_to_write:
            json.dump(self.json_result(), json_result_file_to_write)

def get_total_time(individual: Individual):
    return individual.get_time()

def get_number_of_nans(individual: Individual):
    return individual.get_nan()

toolbox = base.Toolbox()


# -----------------------
# operator registration
# -----------------------
def main():
    random.seed(169)

    try:
        os.mkdir(PATH_TO_TACTICS)
    except:
        print("Oops! The directory for parameters already exists. Anyway, we keep going.")

    # create an initial population of 20 individuals (where each individual is a list of integers)
    individual_ids = list(range(0, POPULATION_SIZE))

    # initialize the population
    population = []
    for individual_id in individual_ids:
        population.append(Individual(population_id=0, individual_id=individual_id, rank=0))

    # evaluate the entire population
    for individual in population:
        individual.evaluate()

    # sort populations
    population.sort(key=get_total_time)
    population.sort(key=get_number_of_nans)

    # set the rank
    rank = 0
    for individual in population:
        individual.set_rank(rank)
        rank = rank + 1

    for individual in population:
        individual.write_json_result()

    # current number of generation
    generation_id = 0

    # begin the evolution
    while all((individual.is_not_good_enough()) for individual in population) \
            and generation_id <= MAXIMUM_NUMBER_OF_GENERATIONS:
        generation_id = generation_id + 1
        print("----- generation %i -----" % generation_id)

        # select the next generation individuals
        offspring1 = population[:POPULATION_SIZE]

        for individual in offspring1:
            individual.set_population_id(generation_id)

        # mutate the best from the previous round
        offspring2 = copy.deepcopy(offspring1) + copy.deepcopy(offspring1[:2])

        # for offspring2, 1) mutate, 2) set ind-id, 3) set generation-id, 4) evaluate
        individual_id = POPULATION_SIZE
        for individual in offspring2:
            individual.mutate()
            individual.set_individual_id(individual_id)
            individual_id = individual_id + 1
            individual.evaluate()

        population[:] = offspring1 + offspring2

        # sort populations
        population.sort(key=get_total_time)
        population.sort(key=get_number_of_nans)
        print("----- population size is %i -----" % len(population))
        rank = 0
        for individual in population:
            print("----- writing result for ind-id %i -----" % individual.individual_id)
            individual.set_rank(rank)
            rank = rank + 1
            individual.write_json_result()

    return 0


if __name__ == "__main__":
    main()
