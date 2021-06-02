import array
import random
import json
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

# define new types
creator.create("FitnessMins", base.Fitness, weights=(-1.0, -1.0,))


class Individual(list):
    """This class describe SuSLik's search strategy for individuals in each population."""

    def __init__(self, population, individual, ordering=None, fitness=creator.FitnessMins):
        if ordering is None:
            ordering = random.sample(range(IND_SIZE), IND_SIZE)
        self.population_id = population
        self.individual_id = individual
        self.rule_ordering = ordering[:]
        self.fitness = fitness

    def mutate(self):
        mutShuffleIndexes(self, indpb=0.05)

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

    #    self.write_json()
    #
    #    results1 = roboevaluation.evaluate_n_times(
    #        1, roboevaluation.METACONFIG1, roboevaluation.CONFIG1, roboevaluation.ALL_BENCHMARKS,
    #        roboevaluation.RESULTS1, roboevaluation.CSV_IN, roboevaluation.CSV_TEMP, True, self.population_id,
    #        self.individual_id)
    #
    #    roboevaluation.write_stats1(roboevaluation.METACONFIG1, roboevaluation.CONFIG1, roboevaluation.ALL_BENCHMARKS,
    #                                results1, self.csv_path())
    #
        df = pandas.read_csv(filepath_or_buffer=self.csv_path(), na_values=['FAIL', '-'])

        number_of_nans = df['Time(mut)'].isna().sum()
        total_time = df['Time(mut)'].sum()

        self.fitness.values = (number_of_nans, total_time)

        return number_of_nans, total_time

toolbox = base.Toolbox()

# attribute generator
# toolbox.register("indices", random.sample, range(IND_SIZE), IND_SIZE)

# structure initializers
# toolbox.register("individual", tools.initIterate, creator.Individual, toolbox.indices)


# -----------------------
# operator registration
# -----------------------

# register the goal

# register the crossover operator
toolbox.register("mate", tools.cxPartialyMatched)

# register a mutation operator with a probability to
# flip each attribute/gene of 0.05
toolbox.register("mutate", tools.mutShuffleIndexes, indpb=0.05)

# register a selection operator: each individual is replaced
# by the best of three randomly drawn individuals.
toolbox.register("select", tools.selTournament, tournsize=3)

def eval_fitness(individual:Individual):
    result = individual.evaluate()
    return result

def main():
    random.seed(169)

    # create an initial population of 20 individuals (where each individual is a list of integers)
    individual_ids = list(range(0, 2))

    # initialize the population
    population = []
    for individual_id in individual_ids:
        population.append (Individual(0, individual_id, None, creator.FitnessMins))

    # evaluate the entire population
    for individual in population:
        individual.evaluate()
        print("individual ID is ")
        print(individual.individual_id)
        print("rule ordering is ")
        print(individual.rule_ordering)
        print("fitness is ")
        print(individual.fitness.values)

    print("---------------")

    for individual in population:
        print("individual ID is ")
        print(individual.individual_id)
        print("rule ordering is ")
        print(individual.rule_ordering)
        print("fitness is ")
        print(individual.fitness.values)

    print("---------------")

    fitnesses = list(map(eval_fitness, population))

    for fit in fitnesses:
        print(fit)

    #
    # call(['java', '-jar', 'target/scala-2.12/suslik.jar', 'src/test/resources/synthesis/paper-benchmarks/ints/swap.syn',
    #       '-t=120000', '--evolutionary', 'true', '--populationID', '3', '--individualID', '12'])
    # call(['java', '-jar', 'target/scala-2.12/suslik.jar', 'src/test/resources/synthesis/paper-benchmarks/ints/swap.syn',
    #       '-t=120000'])
    return 0


if __name__ == "__main__":
    main()
