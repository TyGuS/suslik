import array
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

PATH_TO_TACTICS = "src/main/scala/org/tygus/suslik/synthesis/tactics/"
DEFAULT_ORDER_JSON = PATH_TO_TACTICS + "defaultOrderOfRules.json"
IND_SIZE = 8
POPULATION_SIZE = 4
MAXIMUM_NUMBER_OF_FAILED_SYNTHESIS = 1
MAXIMUM_TOTAL_TIME = 50.0
MAXIMUM_NUMBER_OF_GENERATIONS = 5

# define new types
creator.create("FitnessMins", base.Fitness, weights=(-1.0, -1.0,))


class Individual(list):
    """This class describe SuSLik's search strategy for individuals in each population."""

    def __init__(self, population_id, individual_id, fitness=(0, 9999999999.0), ordering=None):
        super().__init__()
        if ordering is None:
            ordering = random.sample(range(IND_SIZE), IND_SIZE)
        self.population_id = population_id
        self.individual_id = individual_id
        self.rule_ordering = ordering
        self.fitness = fitness

    def get_fitness(self):
        return self.fitness

    def set_fitness(self, pair):
        self.fitness = pair

    def mutate(self):
        tools.mutShuffleIndexes(self.rule_ordering, indpb=0.05)

    def json_file_path(self):
        json_file_name = "orderOfRules" + "_" + str(self.population_id) + "_" + str(self.individual_id) + ".json"
        path = PATH_TO_TACTICS + json_file_name
        return path

    def write_json(self):

        json_data_to_write = {
            "numbOfAnyPhaseRules": IND_SIZE,
            "orderOfAnyPhaseRules": self.rule_ordering
        }

        with open(self.json_file_path(), 'w') as new_json_file_to_write:
            json.dump(json_data_to_write, new_json_file_to_write)

    def csv_path(self):
        path = roboevaluation.EVAL_FOLDER + '/stats-performance_' + str(self.population_id) + '_' + str(
            self.individual_id) + '.csv'
        return path

    def evaluate(self):

        self.write_json()

        results1 = roboevaluation.evaluate_n_times(
            1, roboevaluation.METACONFIG1, roboevaluation.CONFIG1, roboevaluation.ALL_BENCHMARKS,
            roboevaluation.RESULTS1, roboevaluation.CSV_IN, roboevaluation.CSV_TEMP, True, self.population_id,
            self.individual_id)

        roboevaluation.write_stats1(roboevaluation.METACONFIG1, roboevaluation.CONFIG1, roboevaluation.ALL_BENCHMARKS,
                                    results1, self.csv_path())

        df = pandas.read_csv(filepath_or_buffer=self.csv_path(), na_values=['FAIL', '-'])

        number_of_nans = df['Time(mut)'].isna().sum()
        total_time = df['Time(mut)'].sum()

        self.fitness = (number_of_nans, total_time)

        return number_of_nans, total_time

    def is_not_good_enough(self):
        return (self.fitness[0] > MAXIMUM_NUMBER_OF_FAILED_SYNTHESIS) or (self.fitness[1] > MAXIMUM_TOTAL_TIME)


def eval_fitness(individual: Individual):
    result = individual.evaluate()
    return result


def get_total_time(individual: Individual):
    return individual.get_fitness()[1]


def get_number_of_nans(individual: Individual):
    return individual.get_fitness()[0]


def select(population):
    population.sort(key=get_total_time)
    population.sort(key=get_number_of_nans)
    best_individuals = population[:POPULATION_SIZE]
    return best_individuals


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
        population.append (Individual(0, individual_id, (0, 0.0), None))

    # evaluate the entire population
    list(map(eval_fitness, population))

    print("----- initial fitness values -----")
    for individual in population:
        print(individual.get_fitness())

    # current number of generation
    generation_id = 0

    # begin the evolution
    while all((individual.is_not_good_enough()) for individual in population) \
            and generation_id <= MAXIMUM_NUMBER_OF_GENERATIONS:
        generation_id = generation_id + 1
        print("----- generation %i -----" % generation_id)

        # select the next generation individuals
        offspring1 = select(population)

        # mutate the best from the previous round
        offspring2 = copy.deepcopy(offspring1)

        for individual in offspring2:
            individual.mutate()

        list(map(eval_fitness, population))

        population[:] = offspring1 + offspring2

        print("----- fitness is -----")
        for individual in population:
            print(individual.get_fitness())

        print("----- the length of population is -----")
        print(len(population))

    return 0


if __name__ == "__main__":
    main()
