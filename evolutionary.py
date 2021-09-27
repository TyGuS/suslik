import os
import random
import json
import copy

import roboevaluation
import pandas
from deap import base
from deap import tools

PATH_TO_TACTICS = "src/main/scala/org/tygus/suslik/synthesis/tactics/parameters/"
NUMB_OF_ANY_PHASE_RULE = 8
NUMB_OF_PURE_PHASE_RULE = 10
NUMB_OF_SYMBOLIC_EXECUTION_RULE = 6
NUMB_OF_UNFOLDING_PHASE_RULE = 5
NUMB_OF_ANY_PHASE_RULE_OR_SPEC_BASED_RULE = 2
NUMB_OF_SKETCH_HOLE = 3
NUMB_OF_POINTER_PHASE_RULE = 4
NUMB_OF_POST_BLOCK_PHASE_RULE = 4
NUMB_OF_CALL_ABDUCTION_RULE = 4
NUMB_OF_UNFOLDING_POST_PHASE_RULE = 3
NUMB_OF_UNFOLDING_NO_UNFOLD_PHASE_RULES = 2
MAXIMUM_NUMBER_OF_FAILED_SYNTHESIS = 0
MAXIMUM_TOTAL_TIME = 50.0
POPULATION_SIZE = 10
MAXIMUM_NUMBER_OF_GENERATIONS = 20
INDPB = 0.1
NUMB_OF_FEATURES = 2
NUMB_OF_FEATURE_COMBINATION = 2 ** NUMB_OF_FEATURES
NUMB_OF_FEATURES_FOR_ANY_PHASE_RULES = 3
NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES = 2 ** NUMB_OF_FEATURES_FOR_ANY_PHASE_RULES
NUMB_OF_FEATURES_FOR_PURE_PHASE_RULES = 1
NUMB_OF_FEATURE_COMBINATIONS_FOR_PURE_PHASE_RULES = 2 ** NUMB_OF_FEATURES_FOR_PURE_PHASE_RULES
NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES = 2
NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES = 2 ** NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES
NUMB_OF_FEATURES_FOR_UNFOLDING_PHASE_RULES = 1
NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_PHASE_RULES = 2 ** NUMB_OF_FEATURES_FOR_UNFOLDING_PHASE_RULES
NUMB_OF_FEATURES_FOR_POST_UNFOLDING_PHASE_RULES = 1
NUMB_OF_FEATURE_COMBINATIONS_FOR_POST_UNFOLDING_PHASE_RULES = 2 ** NUMB_OF_FEATURES_FOR_POST_UNFOLDING_PHASE_RULES


class Individual(list):
    """This class describe SuSLik's search strategy for individuals in each generation of each group."""

    def __init__(self,
                 group_id,  # group_id = 0 corresponds to initial group created by mutating the manually tuned one.
                 generation_id,
                 individual_id,
                 rank,
                 nan=100,
                 time=9999999999.0,
                 ancestors=None,
                 ancestor_ranks=None,
                 orders_of_any_phase_rules=None,
                 orders_of_pure_phase_rules=None,
                 orders_of_symbolic_execution_rules=None,
                 orders_of_unfolding_phase_rules=None,
                 orders_of_any_phase_rules_or_spec_based_rules=None,
                 orders_of_sketch_hole=None,
                 orders_of_pointer_phase_rules=None,
                 orders_of_post_block_phase_rules=None,
                 orders_of_call_abduction_rules=None,
                 orders_of_unfolding_post_phase_rules=None,
                 orders_of_unfolding_no_unfold_phase_rules=None,
                 weight_of_cost_no_call_goal_pre: float = 3.0,
                 weight_of_cost_no_call_goal_post: float = 1.0,
                 weight_of_cost_call_goal: float = 10.0,
                 weight_of_cost_call_goal_pre: float = 3.0,
                 weight_of_cost_call_goal_post: float = 1.0):
        super().__init__()
        self.group_id = group_id
        self.generation_id = generation_id
        self.individual_id = individual_id
        self.rank = rank
        self.nan = nan
        self.time = time
        self.weight_of_cost_no_call_goal_pre = weight_of_cost_no_call_goal_pre
        self.weight_of_cost_no_call_goal_post = weight_of_cost_no_call_goal_post
        self.weight_of_cost_call_goal = weight_of_cost_call_goal
        self.weight_of_cost_call_goal_pre = weight_of_cost_call_goal_pre
        self.weight_of_cost_call_goal_post = weight_of_cost_call_goal_post

        if ancestors is None:
            ancestors = []
        self.ancestors = ancestors

        if ancestor_ranks is None:
            ancestor_ranks = []
        self.ancestor_ranks = ancestor_ranks

        if orders_of_any_phase_rules is None:
            orders_of_any_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES):
                orders_of_any_phase_rules.append(random.sample(range(NUMB_OF_ANY_PHASE_RULE), NUMB_OF_ANY_PHASE_RULE))
        self.orders_of_any_phase_rules = orders_of_any_phase_rules

        if orders_of_pure_phase_rules is None:
            orders_of_pure_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_PURE_PHASE_RULES):
                orders_of_pure_phase_rules.append \
                    (random.sample(range(NUMB_OF_PURE_PHASE_RULE), NUMB_OF_PURE_PHASE_RULE))
        self.orders_of_pure_phase_rules = orders_of_pure_phase_rules

        if orders_of_symbolic_execution_rules is None:
            orders_of_symbolic_execution_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_symbolic_execution_rules.append \
                    (random.sample(range(NUMB_OF_SYMBOLIC_EXECUTION_RULE), NUMB_OF_SYMBOLIC_EXECUTION_RULE))
        self.orders_of_symbolic_execution_rules = orders_of_symbolic_execution_rules

        if orders_of_unfolding_phase_rules is None:
            orders_of_unfolding_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_PHASE_RULES):
                orders_of_unfolding_phase_rules.append \
                    (random.sample(range(NUMB_OF_UNFOLDING_PHASE_RULE), NUMB_OF_UNFOLDING_PHASE_RULE))
        self.orders_of_unfolding_phase_rules = orders_of_unfolding_phase_rules

        if orders_of_any_phase_rules_or_spec_based_rules is None:
            orders_of_any_phase_rules_or_spec_based_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES):
                orders_of_any_phase_rules_or_spec_based_rules.append \
                    (random.sample(range(NUMB_OF_ANY_PHASE_RULE_OR_SPEC_BASED_RULE),
                                   NUMB_OF_ANY_PHASE_RULE_OR_SPEC_BASED_RULE))
        self.orders_of_any_phase_rules_or_spec_based_rules = orders_of_any_phase_rules_or_spec_based_rules

        if orders_of_sketch_hole is None:
            orders_of_sketch_hole = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_sketch_hole.append(random.sample(range(NUMB_OF_SKETCH_HOLE), NUMB_OF_SKETCH_HOLE))
        self.orders_of_sketch_hole = orders_of_sketch_hole

        if orders_of_pointer_phase_rules is None:
            orders_of_pointer_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_pointer_phase_rules.append \
                    (random.sample(range(NUMB_OF_POINTER_PHASE_RULE), NUMB_OF_POINTER_PHASE_RULE))
        self.orders_of_pointer_phase_rules = orders_of_pointer_phase_rules

        if orders_of_post_block_phase_rules is None:
            orders_of_post_block_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_post_block_phase_rules.append \
                    (random.sample(range(NUMB_OF_POST_BLOCK_PHASE_RULE), NUMB_OF_POST_BLOCK_PHASE_RULE))
        self.orders_of_post_block_phase_rules = orders_of_post_block_phase_rules

        if orders_of_call_abduction_rules is None:
            orders_of_call_abduction_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES):
                orders_of_call_abduction_rules.append \
                    (random.sample(range(NUMB_OF_CALL_ABDUCTION_RULE), NUMB_OF_CALL_ABDUCTION_RULE))
        self.orders_of_call_abduction_rules = orders_of_call_abduction_rules

        if orders_of_unfolding_post_phase_rules is None:
            orders_of_unfolding_post_phase_rules = []
            for i in range(NUMB_OF_FEATURES_FOR_POST_UNFOLDING_PHASE_RULES):
                orders_of_unfolding_post_phase_rules.append \
                    (random.sample(range(NUMB_OF_UNFOLDING_POST_PHASE_RULE), NUMB_OF_UNFOLDING_POST_PHASE_RULE))
        self.orders_of_unfolding_post_phase_rules = orders_of_unfolding_post_phase_rules

        if orders_of_unfolding_no_unfold_phase_rules is None:
            orders_of_unfolding_no_unfold_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_unfolding_no_unfold_phase_rules.append \
                    (random.sample(range(NUMB_OF_UNFOLDING_NO_UNFOLD_PHASE_RULES),
                                   NUMB_OF_UNFOLDING_NO_UNFOLD_PHASE_RULES))
        self.orders_of_unfolding_no_unfold_phase_rules = orders_of_unfolding_no_unfold_phase_rules

    def get_group_id(self):
        return self.group_id

    def set_group_id(self, group_id):
        self.group_id = group_id

    def get_individual_id(self):
        return self.individual_id

    def set_individual_id(self, individual_id):
        self.individual_id = individual_id

    def get_generation_id(self):
        return self.generation_id

    def set_generation_id(self, generation_id):
        self.generation_id = generation_id

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

    def update_ancestor_with_current_individual_id(self):
        self.ancestors.append(self.individual_id)

    def update_ancestor_ranks_with_current_rank(self):
        self.ancestor_ranks.append(self.rank)

    def mutate(self):  # TODO: refactor
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
        for order_of_pointer_phase_rules in self.orders_of_pointer_phase_rules:
            tools.mutShuffleIndexes(order_of_pointer_phase_rules, indpb=INDPB)
        for order_of_post_block_phase_rule in self.orders_of_post_block_phase_rules:
            tools.mutShuffleIndexes(order_of_post_block_phase_rule, indpb=INDPB)
        for order_of_call_abduction_rules in self.orders_of_call_abduction_rules:
            tools.mutShuffleIndexes(order_of_call_abduction_rules, indpb=INDPB)
        for order_of_unfolding_post_phase_rules in self.orders_of_unfolding_post_phase_rules:
            tools.mutShuffleIndexes(order_of_unfolding_post_phase_rules, indpb=INDPB)
        for order_of_unfolding_no_unfold_phase_rules in self.orders_of_unfolding_no_unfold_phase_rules:
            tools.mutShuffleIndexes(order_of_unfolding_no_unfold_phase_rules, indpb=INDPB)
        self.weight_of_cost_no_call_goal_pre = self.weight_of_cost_call_goal_pre * random.uniform(0.8, 1.2)
        self.weight_of_cost_no_call_goal_post = self.weight_of_cost_call_goal_post * random.uniform(0.8, 1.2)
        self.weight_of_cost_call_goal = self.weight_of_cost_call_goal * random.uniform(0.8, 1.2)
        self.weight_of_cost_call_goal_pre = self.weight_of_cost_call_goal_pre * random.uniform(0.8, 1.2)
        self.weight_of_cost_call_goal_post = self.weight_of_cost_call_goal_post * random.uniform(0.8, 1.2)

    # TODO: This only supports the static optimisation. (compiler-time optimisation)
    # TODO: The use of the * opeartor is WRONG! FIXME. Use append.
    def default(self):

        orders_of_any_phase_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES)):
            orders_of_any_phase_rules.append(list(range(0, NUMB_OF_ANY_PHASE_RULE)))
        self.orders_of_any_phase_rules = orders_of_any_phase_rules

        orders_of_pure_phase_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_PURE_PHASE_RULES)):
            orders_of_pure_phase_rules.append(list(range(0, NUMB_OF_PURE_PHASE_RULE)))
        self.orders_of_pure_phase_rules = orders_of_pure_phase_rules

        orders_of_symbolic_execution_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATION)):
            orders_of_symbolic_execution_rules.append(list(range(0, NUMB_OF_SYMBOLIC_EXECUTION_RULE)))
        self.orders_of_symbolic_execution_rules = orders_of_symbolic_execution_rules

        orders_of_unfolding_phase_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_PHASE_RULES)):
            orders_of_unfolding_phase_rules.append(list(range(0, NUMB_OF_UNFOLDING_PHASE_RULE)))
        self.orders_of_unfolding_phase_rules = orders_of_unfolding_phase_rules

        orders_of_any_phase_rules_or_spec_based_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES)):
            orders_of_any_phase_rules_or_spec_based_rules.append(list(range(0, NUMB_OF_ANY_PHASE_RULE_OR_SPEC_BASED_RULE)))
        self.orders_of_any_phase_rules_or_spec_based_rules = orders_of_any_phase_rules_or_spec_based_rules

        orders_of_sketch_hole = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATION)):
            orders_of_sketch_hole.append(list(range(0, NUMB_OF_SKETCH_HOLE)))
        self.orders_of_sketch_hole = orders_of_sketch_hole

        orders_of_pointer_phase_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATION)):
            orders_of_pointer_phase_rules.append(list(range(0, NUMB_OF_POINTER_PHASE_RULE)))
        self.orders_of_pointer_phase_rules = orders_of_pointer_phase_rules

        orders_of_post_block_phase_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATION)):
            orders_of_post_block_phase_rules.append(list(range(0, NUMB_OF_POST_BLOCK_PHASE_RULE)))
        self.orders_of_post_block_phase_rules = orders_of_post_block_phase_rules

        orders_of_call_abduction_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES)):
            orders_of_call_abduction_rules.append(list(range(0, NUMB_OF_CALL_ABDUCTION_RULE)))
        self.orders_of_call_abduction_rules = orders_of_call_abduction_rules

        orders_of_unfolding_post_phase_rules = []
        for i in list(range(NUMB_OF_FEATURES_FOR_POST_UNFOLDING_PHASE_RULES)):
            orders_of_unfolding_post_phase_rules.append(list(range(0, NUMB_OF_UNFOLDING_POST_PHASE_RULE)))
        self.orders_of_unfolding_post_phase_rules = orders_of_unfolding_post_phase_rules

        orders_of_unfolding_no_unfold_phase_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATION)):
            orders_of_unfolding_no_unfold_phase_rules.append(list(range(0, NUMB_OF_UNFOLDING_NO_UNFOLD_PHASE_RULES)))
        self.orders_of_unfolding_no_unfold_phase_rules = orders_of_unfolding_no_unfold_phase_rules

        self.weight_of_cost_no_call_goal_pre = 3.0
        self.weight_of_cost_no_call_goal_post = 1.0
        self.weight_of_cost_call_goal = 10.0
        self.weight_of_cost_call_goal_pre = 3.0
        self.weight_of_cost_call_goal_post = 1.0

    def json_file_path(self):
        json_file_name = "search_parameter" + "_" + str(self.group_id) + "_" + str(self.generation_id) + "_" + \
                         str(self.individual_id) + ".json"
        path = PATH_TO_TACTICS + json_file_name
        return path

    def write_order_json(self):

        json_data_to_write = {
            "orders_of_any_phase_rules": self.orders_of_any_phase_rules,
            "orders_of_pure_phase_rules": self.orders_of_pure_phase_rules,
            "orders_of_symbolic_execution_rules": self.orders_of_symbolic_execution_rules,
            "orders_of_unfolding_phase_rules": self.orders_of_unfolding_phase_rules,
            "orders_of_any_phase_rules_or_spec_based_rules": self.orders_of_any_phase_rules_or_spec_based_rules,
            "orders_of_sketch_hole": self.orders_of_sketch_hole,
            "orders_of_pointer_phase_rules": self.orders_of_pointer_phase_rules,
            "orders_of_post_block_phase_rules": self.orders_of_post_block_phase_rules,
            "orders_of_call_abduction_rules": self.orders_of_call_abduction_rules,
            "orders_of_unfolding_post_phase_rules": self.orders_of_unfolding_post_phase_rules,
            "orders_of_unfolding_no_unfold_phase_rules": self.orders_of_unfolding_no_unfold_phase_rules,
            "weight_of_cost_no_call_goal_pre": self.weight_of_cost_no_call_goal_pre,
            "weight_of_cost_no_call_goal_post": self.weight_of_cost_no_call_goal_post,
            "weight_of_cost_call_goal": self.weight_of_cost_call_goal,
            "weight_of_cost_call_goal_pre": self.weight_of_cost_call_goal_pre,
            "weight_of_cost_call_goal_post": self.weight_of_cost_call_goal_post
        }

        with open(self.json_file_path(), 'w') as new_json_file_to_write:
            json.dump(json_data_to_write, new_json_file_to_write)

    def csv_path(self, is_for_training=True):

        if is_for_training:
            result_type = "_training_"
        else:
            result_type = "_validation_"

        path = roboevaluation.EVAL_FOLDER + '/stats-performance' + result_type + str(self.group_id) + "_" \
               + str(self.generation_id) + '_' + str(self.individual_id) + '.csv'
        return path

    def evaluate(self, for_training=True):

        self.write_order_json()
        if for_training:
            data = roboevaluation.TRAINING_DATA
        else:
            data = roboevaluation.VALIDATION_DATA

        results1 = roboevaluation.evaluate_n_times(
            1, roboevaluation.METACONFIG1, roboevaluation.CONFIG1, data,
            roboevaluation.RESULTS1, roboevaluation.CSV_IN, roboevaluation.CSV_TEMP, True,
            self.group_id, self.generation_id, self.individual_id)

        roboevaluation.write_stats1(roboevaluation.METACONFIG1, roboevaluation.CONFIG1, data,
                                    results1, self.csv_path(is_for_training=for_training))

        df = pandas.read_csv(filepath_or_buffer=self.csv_path(is_for_training=for_training), na_values=['FAIL', '-'])

        number_of_nans = int(df['Time(mut)'].isna().sum())
        total_time = df['Time(mut)'].sum()

        self.nan, self.time = (number_of_nans, total_time)

        return number_of_nans, total_time

    # Note that we use the rank of individual in the file name.
    def json_result_file_path(self, is_for_training=True):

        if is_for_training:
            result_type = "_training_"
        else:
            result_type = "_validation_"

        return "robo-evaluation-utils/result" + result_type + str(self.group_id) + "_" + str(self.generation_id) + "_" \
               + str(self.rank) + ".json"

    def json_overall_result_file_path(self, is_for_training=True):

        if is_for_training:
            result_type = "_overall_training_"
        else:
            result_type = "_overall_validation_"

        return "robo-evaluation-utils/result" + result_type + str(self.group_id) + ".json"

    def json_result(self, is_for_training=True):
        return {
            "group_ID": self.group_id,
            "generation_ID": self.generation_id,
            "individual_ID": self.individual_id,
            "rank": self.rank,
            "number_of_nan": self.nan,
            "search_time": self.time,
            "ancestors": self.ancestors,
            "ancestor_ranks": self.ancestor_ranks,
            "is_for_training": is_for_training,
            "weight_of_cost_no_call_goal_pre": self.weight_of_cost_no_call_goal_pre,
            "weight_of_cost_no_call_goal_post": self.weight_of_cost_no_call_goal_post,
            "weight_of_cost_call_goal": self.weight_of_cost_call_goal,
            "weight_of_cost_call_goal_pre": self.weight_of_cost_call_goal_pre,
            "weight_of_cost_call_goal_post": self.weight_of_cost_call_goal_post
        }

    def write_json_result(self, for_training=True):

        with open(self.json_result_file_path(for_training), 'w') as json_result_file_to_write:
            json.dump(self.json_result(for_training), json_result_file_to_write)

    def write_overall_json_result(self, for_training=True):
        with open(self.json_overall_result_file_path(for_training), 'a') as \
                json_overall_validation_result_file_to_write:
            json.dump(self.json_result(for_training), json_overall_validation_result_file_to_write)
            json_overall_validation_result_file_to_write.write("\n")
            json_overall_validation_result_file_to_write.close()


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

    # evaluate the default strategy
    default = Individual(group_id=0, generation_id=0, individual_id=0, rank=0)
    default.default()
    #default.evaluate(for_training=False)
    #default.write_json_result(for_training=False)
    #default.write_overall_json_result(for_training=False)
    #default.evaluate(for_training=True)
    #default.write_json_result(for_training=True)
    #default.write_overall_json_result(for_training=True)

    # create an initial groups of POPULATION_SIZE individuals
    generation_id = 1
    individual_ids = list(range(0, POPULATION_SIZE))

    # group_m is a group that starts at the manually tuned parameters.
    group_m = []
    for individual_id in individual_ids:
        new_individual = copy.deepcopy(default)
        new_individual.set_group_id(0)
        new_individual.set_individual_id(individual_id)
        new_individual.set_generation_id(generation_id)
        new_individual.mutate()
        group_m.append(new_individual)

    group_a = []
    # group_B = []
    for individual_id in individual_ids:
        group_a.append(Individual(group_id=1, generation_id=generation_id, individual_id=individual_id, rank=0))
        # group_B.append(Individual(group_id=2, generation_id=generation_id, individual_id=individual_id, rank=0))

    groups = [group_m]#, group_a]  # , group_B]

    # evaluate all groups
    for group in groups:
        for individual in group:
            individual.evaluate()

    # sort each group
    for group in groups:
        group.sort(key=get_total_time)
        group.sort(key=get_number_of_nans)

    # set the rank, write resulting JSON file
    for group in groups:
        rank = 0
        for individual in group:
            individual.set_rank(rank)
            rank = rank + 1
            individual.write_json_result()

    for group in groups:
        best_individual_so_far = copy.deepcopy(group[0])
        best_individual_so_far.write_overall_json_result(for_training=True)
        best_individual_so_far.evaluate(for_training=False)
        best_individual_so_far.write_json_result(for_training=False)
        best_individual_so_far.write_overall_json_result(for_training=False)

    # begin the evolution
    while generation_id <= MAXIMUM_NUMBER_OF_GENERATIONS:
        generation_id = generation_id + 1
        print("----- generation %i -----" % generation_id)

        for group in groups:

            # select the next generation individuals
            offspring1 = group[:POPULATION_SIZE]

            # firstly update ancestors using the current individual_id
            for individual in offspring1:
                individual.update_ancestor_with_current_individual_id()
                individual.update_ancestor_ranks_with_current_rank()

            # secondly update individual_id of offspring1 (the ones that survived the previous selection)
            individual_id = 0
            for individual in offspring1:
                individual.set_individual_id(individual_id)
                individual_id = individual_id + 1

            for individual in offspring1:
                individual.set_generation_id(generation_id)

            # copy the best ones from the previous round.
            offspring2 = copy.deepcopy(offspring1) + copy.deepcopy(offspring1[:2])

            # for offspring2, 1) mutate, 2) set ind-id, 3) set individual_id, 4) evaluate
            for individual in offspring2:
                individual.mutate()
                individual.set_individual_id(individual_id)
                individual_id = individual_id + 1
                individual.evaluate()

            group[:] = offspring1 + offspring2

            # sort group
            group.sort(key=get_total_time)
            group.sort(key=get_number_of_nans)

            rank = 0
            for individual in group:
                print("----- writing result for ind-id %i -----" % individual.individual_id)
                individual.set_rank(rank)
                rank = rank + 1
                individual.write_json_result()

            best_individual_so_far = copy.deepcopy(group[0])
            best_individual_so_far.write_overall_json_result(for_training=True)
            print("----- cross validation for generation number %i -----" % best_individual_so_far.individual_id)
            best_individual_so_far.evaluate(for_training=False)
            best_individual_so_far.write_json_result(for_training=False)
            best_individual_so_far.write_overall_json_result(for_training=False)

    return 0


if __name__ == "__main__":
    main()