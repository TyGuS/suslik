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
DEFAULT_ORDER_JSON = PATH_TO_TACTICS + "defaultOrderOfRules.json"
IND_SIZE = 8
MAXIMUM_NUMBER_OF_FAILED_SYNTHESIS = 0
MAXIMUM_TOTAL_TIME = 50.0
POPULATION_SIZE = 5
MAXIMUM_NUMBER_OF_GENERATIONS = 50
INDPB = 0.2

class Individual(list):
    """This class describe SuSLik's search strategy for individuals in each population."""

    def __init__(self, population_id, individual_id, nan=10, time=9999999999.0 , rule_ordering=None,
                 weight_of_cost_no_call_goal_pre=3.0, weight_of_cost_no_call_goal_post=1.0,
                 weight_of_cost_call_goal=10.0, weight_of_cost_call_goal_pre=3.0, weight_of_cost_call_goal_post=1.0):
        super().__init__()
        if rule_ordering is None:
            rule_ordering = random.sample(range(IND_SIZE), IND_SIZE)
        self.population_id = population_id
        self.individual_id = individual_id
        self.rule_ordering = rule_ordering
        self.nan = nan,
        self.time = time,
        self.weight_of_cost_no_call_goal_pre = weight_of_cost_no_call_goal_pre,
        self.weight_of_cost_no_call_goal_post = weight_of_cost_no_call_goal_post,
        self.weight_of_cost_call_goal = weight_of_cost_call_goal,
        self.weight_of_cost_call_goal_pre = weight_of_cost_call_goal_pre,
        self.weight_of_cost_call_goal_post = weight_of_cost_call_goal_post,
        self.json_search_parameter_file_path = PATH_TO_TACTICS + "search_parameters_" + str(population_id) + "_" + str(individual_id) + ".json"

    def get_individual_id(self):
        return self.individual_id

    def set_individual_id(self, individual_id):
        self.individual_id = individual_id

    def set_population_id(self, population_id):
        self.population_id = population_id

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

    def write_json_search_parameter_file(self):

        json_search_parameter_to_write = {
            "order_of_any_phase_rules": self.rule_ordering,
            "weight_of_cost_no_call_goal_pre": self.weight_of_cost_no_call_goal_pre,
            "weight_of_cost_no_call_goal_post": self.weight_of_cost_no_call_goal_post,
            "weight_of_cost_call_goal": self.weight_of_cost_call_goal,
            "weight_of_cost_call_goal_pre": self.weight_of_cost_call_goal_pre,
            "weight_of_cost_call_goal_post": self.weight_of_cost_call_goal_post
        }

        with open(self.json_search_parameter_file_path, 'w') as new_json_file_to_write:
            json.dump(json_search_parameter_to_write, new_json_file_to_write)

    def csv_path(self):
        path = roboevaluation.EVAL_FOLDER + '/stats-performance_' + str(self.population_id) + '_' + str(
            self.individual_id) + '.csv'
        return path

    def evaluate(self):

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

    def json_result_file_path(self):
        return "robo-evaluation-utils/result" + "_" + str(self.population_id) + "_" + str(self.individual_id) \
                         + ".json"

    def json_result(self):
        return {
            "generation_ID": self.population_id,
            "individual_ID": self.individual_id,
            "number_of_nan": self.nan,
            "search_time": self.time,
            "rule_ordering": self.rule_ordering
        }

    def write_json_result(self):

        with open(self.json_result_file_path(), 'w') as json_result_file_to_write:
            json.dump(json_result(), json_result_file_to_write)


def write_json_search_parameters(individual:Individual):
    individual.write_json_search_parameter_file()


def eval_fitness(individual: Individual):
    result = individual.evaluate()
    return result


def get_total_time(individual: Individual):
    return individual.get_time()


def get_number_of_nans(individual: Individual):
    return individual.get_nan()


def select(population):
    population.sort(key=get_total_time)
    population.sort(key=get_number_of_nans)
    best_individuals = population[:POPULATION_SIZE]
    return best_individuals


def json_result_file_path(generation_id: int):
    return "robo-evaluation-utils/result" + "_" + str(generation_id) + ".json"


def write_json_result(generation_id, population):
    path = json_result_file_path(generation_id)
    json_data = {
        "generation_id": generation_id,
        "number_of_nan": list(map(get_number_of_nans, population)),
        "total_time": list(map(get_total_time, population))
    }
    with open(path, 'w') as file:
        json.dump(json_data, file)


toolbox = base.Toolbox()


# -----------------------
# operator registration
# -----------------------
def main():
    random.seed(169)

    # create an initial population of 20 individuals (where each individual is a list of integers)
    individual_ids = list(range(0, POPULATION_SIZE))

    # initialize the population
    population = []
    for individual_id in individual_ids:
        population.append(Individual(0, individual_id, 0, 0.0, None))

    # write down json files containing search parameters
    list(map(write_json_search_parameters, population))

    # evaluate the entire population
    list(map(eval_fitness, population))

    print("----- initial nan and time -----")
    for individual in population:
        print(individual.get_nan())
        print(individual.get_time())

    # current number of generation
    generation_id = 0

    # begin the evolution
    while all((individual.is_not_good_enough()) for individual in population) \
            and generation_id <= MAXIMUM_NUMBER_OF_GENERATIONS:
        generation_id = generation_id + 1
        print("----- generation %i -----" % generation_id)

        for individual in population:
            individual.set_population_id(generation_id)

        # select the next generation individuals
        offspring1 = select(population)

        # mutate the best from the previous round
        offspring2 = copy.deepcopy(offspring1)

        for individual in offspring2:
            individual.mutate()

        # write down json files containing search parameters
        list(map(write_json_search_parameters, population))

        # evaluate the entire population
        list(map(eval_fitness, offspring2))

        population[:] = offspring1 + offspring2

        individual_id = 0

        for individual in population:
            individual.set_individual_id(individual_id)
            individual_id = individual_id + 1

        write_json_result(generation_id, population)

        print("----- fitness is -----")
        for individual in population:
            print(individual.get_nan())
            print(individual.get_time())

        print("----- the length of population is -----")
        print(len(population))

    return 0


if __name__ == "__main__":
    main()
