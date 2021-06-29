import array
import random
import json
import copy
from subprocess import call

import roboevaluation

import numpy
import pandas
import os

from deap import algorithms
from deap import base
from deap import creator
from deap import tools

PATH_TO_TACTICS = "src/main/scala/org/tygus/suslik/synthesis/tactics/parameters/"
IND_SIZE = 8
MAXIMUM_NUMBER_OF_FAILED_SYNTHESIS = 0
MAXIMUM_TOTAL_TIME = 50.0
GENERATION_SIZE = 10
MAXIMUM_NUMBER_OF_GENERATIONS = 50
INDPB = 0.1

class Individual(list):
    """This class describe SuSLik's search strategy for individuals in each generation."""

    def __init__(self, generation_id,
                 individual_id,
                 nan=10,
                 time=9999999999.0,
                 rule_ordering=None,
                 weight_of_cost_no_call_goal_pre: float = 3.0,
                 weight_of_cost_no_call_goal_post: float = 1.0,
                 weight_of_cost_call_goal: float = 10.0,
                 weight_of_cost_call_goal_pre: float = 3.0,
                 weight_of_cost_call_goal_post: float = 1.0):
        super().__init__()
        if rule_ordering is None:
            rule_ordering = random.sample(range(IND_SIZE), IND_SIZE)
        self.generation_id = generation_id
        self.individual_id = individual_id
        self.rule_ordering = rule_ordering
        self.nan = nan
        self.time = time
        self.weight_of_cost_no_call_goal_pre = weight_of_cost_no_call_goal_pre
        self.weight_of_cost_no_call_goal_post = weight_of_cost_no_call_goal_post
        self.weight_of_cost_call_goal = weight_of_cost_call_goal
        self.weight_of_cost_call_goal_pre = weight_of_cost_call_goal_pre
        self.weight_of_cost_call_goal_post = weight_of_cost_call_goal_post

    def json_search_parameter_file_path(self):
        return PATH_TO_TACTICS + "search_parameters_" + str(self.generation_id) + "_" + str(self.individual_id) + ".json"

    def get_individual_id(self):
        return self.individual_id

    def set_individual_id(self, individual_id):
        self.individual_id = individual_id

    def set_generation_id(self, generation_id):
        self.generation_id = generation_id

    def get_time(self):
        return self.time

    def set_time(self, time):
        self.time = time

    def get_nan(self):
        return self.nan

    def set_nan(self, nan):
        self.nan = nan

    def set_weight_of_cost_no_call_goal_pre(self, weight_of_cost_no_call_goal_pre):
        self.weight_of_cost_no_call_goal_pre = weight_of_cost_no_call_goal_pre

    def get_weight_of_cost_no_call_goal_pre(self):
        return self.weight_of_cost_no_call_goal_pre

    def set_weight_of_cost_no_call_goal_post(self, weight_of_cost_no_call_goal_post):
        self.weight_of_cost_no_call_goal_post = weight_of_cost_no_call_goal_post

    def get_weight_of_cost_no_call_goal_post(self):
        return self.weight_of_cost_no_call_goal_post

    def set_weight_of_cost_call_goal(self, weight_of_cost_call_goal):
        self.weight_of_cost_call_goal = weight_of_cost_call_goal

    def get_weight_of_cost_call_goal(self):
        return self.weight_of_cost_call_goal

    def set_weight_of_cost_call_goal_pre(self, weight_of_cost_call_goal_pre):
        self.weight_of_cost_call_goal_pre = weight_of_cost_call_goal_pre

    def get_weight_of_cost_call_goal_pre(self):
        return self.weight_of_cost_call_goal_pre

    def set_weight_of_cost_call_goal_post(self, weight_of_cost_call_goal_post):
        self.weight_of_cost_call_goal_post = weight_of_cost_call_goal_post

    def get_weight_of_cost_call_goal_post(self):
        return self.weight_of_cost_call_goal_post

    def mutate(self):
        tools.mutShuffleIndexes(self.rule_ordering, indpb=INDPB)
        self.weight_of_cost_no_call_goal_pre = self.weight_of_cost_call_goal_pre * random.uniform(0.8, 1.2)
        self.weight_of_cost_no_call_goal_post = self.weight_of_cost_call_goal_post * random.uniform(0.8, 1.2)
        self.weight_of_cost_call_goal = self.weight_of_cost_call_goal * random.uniform(0.8, 1.2)
        self.weight_of_cost_call_goal_pre = self.weight_of_cost_call_goal_pre * random.uniform(0.8, 1.2)
        self.weight_of_cost_call_goal_post = self.weight_of_cost_call_goal_post * random.uniform(0.8, 1.2)

    def write_json_search_parameter_file(self):

        json_search_parameter_to_write = {
            "order_of_any_phase_rules": self.rule_ordering,
            "weight_of_cost_no_call_goal_pre": self.weight_of_cost_no_call_goal_pre,
            "weight_of_cost_no_call_goal_post": self.weight_of_cost_no_call_goal_post,
            "weight_of_cost_call_goal": self.weight_of_cost_call_goal,
            "weight_of_cost_call_goal_pre": self.weight_of_cost_call_goal_pre,
            "weight_of_cost_call_goal_post": self.weight_of_cost_call_goal_post
        }

        with open(self.json_search_parameter_file_path(), 'w') as new_json_file_to_write:
            json.dump(json_search_parameter_to_write, new_json_file_to_write)

    def csv_path(self):
        path = roboevaluation.EVAL_FOLDER + '/stats-performance_' + str(self.generation_id) + '_' + str(
            self.individual_id) + '.csv'
        return path

    def evaluate(self):

        results1 = roboevaluation.evaluate_n_times(
            1, roboevaluation.METACONFIG1, roboevaluation.CONFIG1, roboevaluation.ALL_BENCHMARKS,
            roboevaluation.RESULTS1, roboevaluation.CSV_IN, roboevaluation.CSV_TEMP, True, self.generation_id,
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

    def json_result_file_path(self):
        return "robo-evaluation-utils/result" + "_" + str(self.generation_id) + "_" + str(self.individual_id) \
                         + ".json"

    def json_result(self):
        return {
            "generation_ID": self.generation_id,
            "individual_ID": self.individual_id,
            "number_of_nan": self.nan,
            "search_time": self.time,
            "rule_ordering": self.rule_ordering
        }

    def write_json_result(self):

        with open(self.json_result_file_path(), 'w') as json_result_file_to_write:
            json.dump(json_result(), json_result_file_to_write)


def select(generation):
    best_individuals = generation[:GENERATION_SIZE]
    return best_individuals


def json_result_file_path(generation_id: int):
    return "robo-evaluation-utils/result" + "_" + str(generation_id) + ".json"

# -----------------------
# operator registration
# -----------------------
def main():
    random.seed(169)

    # create an initial generation of 20 individuals (where each individual is a list of integers)
    individual_ids = list(range(0, GENERATION_SIZE))

    # initialize the generation
    generation = []
    for individual_id in individual_ids:
        generation.append(Individual(0, individual_id, 0, 0.0, None))

    # write down json files containing search parameters
    for individual in generation:
        individual.write_json_search_parameter_file()

    # evaluate the entire generation
    for individual in generation:
        individual.evaluate()

    # current number of generation
    generation_id = 0

    write_json_result(generation_id, generation)

    offspring1 = generation[:]

    # begin the evolution
    while all((individual.is_not_good_enough()) for individual in generation) \
            and generation_id <= MAXIMUM_NUMBER_OF_GENERATIONS:

        # mutate the best from the previous round
        offspring2 = copy.deepcopy(offspring1)

        for individual in offspring2:
            individual.mutate()

        generation[:] = offspring1 + offspring2

        # update generation_id
        generation_id = generation_id + 1
        print("----- generation %i -----" % generation_id)
        for individual in generation:
            individual.set_generation_id(generation_id)

        # update individual_id
        individual_id = 0
        for individual in generation:
            individual.set_individual_id(individual_id)
            individual_id = individual_id + 1

        # write down json files containing search parameters
        for individual in generation:
            individual.write_json_search_parameter_file()

        # evaluate the entire generation
        for individual in offspring2:
            individual.evaluate()

        write_json_result(generation_id, generation)

        # sort and select the next generation individuals
        generation.sort(key=get_total_time)
        generation.sort(key=get_number_of_nans)
        offspring1 = select(generation)

    return 0


if __name__ == "__main__":
    main()
