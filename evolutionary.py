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


class Strategy:
    """This class describe SuSLik's search strategy."""

    def __init__(self, population=0, individual=0, ordering=None):
        if ordering is None:
            ordering = [0, 1, 2, 3, 4, 5, 6, 7]
        self.population_id = population
        self.individual_id = individual
        self.rule_ordering = ordering[:]

    def mutate(self):
        mutShuffleIndexes(self, indpb=0.05)

    def json_file_path(self):
        json_file_name = "orderOfRules" + "_" + str(self.population_id) + "_" + str(self.individual_id) + ".json"
        path = PATH_TO_TACTICS + json_file_name
        return path

    def csv_path(self):
        path = roboevaluation.EVAL_FOLDER + '/stats-performance_' + str(self.population_id) + '_' + str(
            self.individual_id) + '.csv'
        return path

    def evaluate(self):
        results1 = roboevaluation.evaluate_n_times(
            1, roboevaluation.METACONFIG1, roboevaluation.CONFIG1, roboevaluation.ALL_BENCHMARKS,
            roboevaluation.RESULTS1, roboevaluation.CSV_IN, roboevaluation.CSV_TEMP, self.population_id,
            self.individual_id)
        roboevaluation.write_stats1(roboevaluation.METACONFIG1, roboevaluation.CONFIG1, roboevaluation.ALL_BENCHMARKS,
                                    results1, csv_path(self))
        df = pandas.read_csv(csv_path(self))
        total_time = df['Time(mut)'].sum()
        return total_time


# define new types
creator.create("FitnessMax", base.Fitness, weights=(1.0,))
creator.create("Individual", list, fitness=creator.FitnessMax)

IND_SIZE = 8

toolbox = base.Toolbox()

# attribute generator
toolbox.register("indices", random.sample, range(IND_SIZE), IND_SIZE)

# structure initializers
toolbox.register("individual", tools.initIterate, creator.Individual, toolbox.indices)

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


def main():
    random.seed(169)

    population_id = 3
    individual_id = 12
    print("individual ID is ")
    print(individual_id)
    print("populationID is ")
    print(population_id)

    with open(DEFAULT_ORDER_JSON, "r") as jsonFile:
        jsonData = json.load(jsonFile)

    numbOfAnyPhaseRules = jsonData["numbOfAnyPhaseRules"]
    orderOfAnyPhaseRules = jsonData["orderOfAnyPhaseRules"]

    reversedOrderOfAnyPhaseRules = orderOfAnyPhaseRules.copy()
    reversedOrderOfAnyPhaseRules.reverse()

    newJsonDataToWrite = {
        "numbOfAnyPhaseRules": numbOfAnyPhaseRules,
        "orderOfAnyPhaseRules": reversedOrderOfAnyPhaseRules
    }

    with open(getJsonFilePath(population_id, individual_id), 'w') as newJsonFileToWrite:
        json.dump(newJsonDataToWrite, newJsonFileToWrite)

    with open(getJsonFilePath(population_id, individual_id), "r") as newJsonFileToRead:
        newJsonDataToRead = json.load(newJsonFileToRead)

    newNumbOfAnyPhaseRules = newJsonDataToRead["numbOfAnyPhaseRules"]
    newOrderOfAnyPhaseRules = newJsonDataToRead["orderOfAnyPhaseRules"]

    print("read a rule-odering from a json file")
    print(numbOfAnyPhaseRules)
    print(orderOfAnyPhaseRules)
    print("reverse")
    print(reversedOrderOfAnyPhaseRules)
    print("write the reversed order to a json file then read it")
    print(newNumbOfAnyPhaseRules)
    print(newOrderOfAnyPhaseRules)

    call(['java', '-jar', 'target/scala-2.12/suslik.jar', 'src/test/resources/synthesis/paper-benchmarks/ints/swap.syn',
          '-t=120000', '--evolutionary', 'true', '--populationID', '3', '--individualID', '12'])
    call(['java', '-jar', 'target/scala-2.12/suslik.jar', 'src/test/resources/synthesis/paper-benchmarks/ints/swap.syn',
          '-t=120000'])
    return 0


if __name__ == "__main__":
    main()
