import os
import random
import json
import copy

import roboevaluation
import pandas
from deap import base
from deap import tools
import math
from typing import List

PATH_TO_TACTICS = "src/main/scala/org/tygus/suslik/synthesis/tactics/parameters/"
NUMB_OF_ANY_PHASE_RULE = 8
NUMB_OF_PURE_PHASE_RULE = 10
NUMB_OF_SYMBOLIC_EXECUTION_RULE = 6
NUMB_OF_UNFOLDING_PHASE_RULE = 5
NUMB_OF_ANY_PHASE_RULE_OR_SPEC_BASED_RULE = 2  # No weights
NUMB_OF_SKETCH_HOLE_RULE = 3
NUMB_OF_POINTER_PHASE_RULE = 4
NUMB_OF_POST_BLOCK_PHASE_RULE = 4
NUMB_OF_CALL_ABDUCTION_RULE_1 = 5
NUMB_OF_CALL_ABDUCTION_RULE_2 = 5
NUMB_OF_CALL_ABDUCTION_RULE_3 = 5
NUMB_OF_CALL_ABDUCTION_RULE_4 = 12
NUMB_OF_UNFOLDING_POST_PHASE_RULE = 3
NUMB_OF_UNFOLDING_NO_UNFOLD_PHASE_RULES = 2
MAXIMUM_NUMBER_OF_FAILED_SYNTHESIS = 0
POPULATION_SIZE = 10
MAXIMUM_NUMBER_OF_GENERATIONS = 10
INDPB = 0.1
STANDARD_DEVIATION = 0.05

FEWER_FEATURE_COMBINATION = True

NUMB_OF_FEATURES = 2
NUMB_OF_FEATURES_FOR_ANY_PHASE_RULES_OR_SPEC_BASED_RULES = 4
NUMB_OF_FEATURES_FOR_ANY_PHASE_RULES = 4
NUMB_OF_FEATURES_FOR_PURE_PHASE_RULES = 4
NUMB_OF_FEATURES_FOR_SYMBOLIC_EXECUTION_PHASE_RULES = 0
NUMB_OF_FEATURES_FOR_UNFOLDING_PHASE_RULES = 3
NUMB_OF_FEATURES_FOR_SKETCH_HOL_RULES = 0
NUMB_OF_FEATURES_FOR_POINTER_PHASE_RULES = 3
NUMB_OF_FEATURES_FOR_UNFOLDING_POST_PHASE_RULES = 3
NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES_1 = 3
NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES_2 = 3
NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES_3 = 3
NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES_4 = 5
NUMB_OF_FEATURES_FOR_POST_BLOCK_PHASE_RULES = 1
NUMB_OF_FEATURES_FOR_UNFOLDING_NO_UNFOLD_PHASE_RULES = 2

if FEWER_FEATURE_COMBINATION:
    NUMB_OF_FEATURE_COMBINATION = 1 + NUMB_OF_FEATURES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES_OR_SPEC_BASED_RULES = \
        1 + NUMB_OF_FEATURES_FOR_ANY_PHASE_RULES_OR_SPEC_BASED_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES = 1 + NUMB_OF_FEATURES_FOR_ANY_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_PURE_PHASE_RULES = 1 + NUMB_OF_FEATURES_FOR_PURE_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_SYMBOLIC_EXECUTION_PHASE_RULES = \
        1 + NUMB_OF_FEATURES_FOR_SYMBOLIC_EXECUTION_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_PHASE_RULES = 1 + NUMB_OF_FEATURES_FOR_UNFOLDING_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATORS_FOR_SKETCH_HOL_RULES = 1 + NUMB_OF_FEATURES_FOR_SKETCH_HOL_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_POST_BLOCK_PHASE_RULES = 1 + NUMB_OF_FEATURES_FOR_POST_BLOCK_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_POINTER_PHASE_RULES = 1 + NUMB_OF_FEATURES_FOR_POINTER_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_1 = 1 + NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES_1
    NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_2 = 1 + NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES_2
    NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_3 = 1 + NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES_3
    NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_4 = 1 + NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES_4
    NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_POST_PHASE_RULES = 1 + NUMB_OF_FEATURES_FOR_UNFOLDING_POST_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_NO_UNFOLD_PHASE_RULES = \
        1 + NUMB_OF_FEATURES_FOR_UNFOLDING_NO_UNFOLD_PHASE_RULES
else:
    NUMB_OF_FEATURE_COMBINATION = 2 ** NUMB_OF_FEATURES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES_OR_SPEC_BASED_RULES = \
        2 ** NUMB_OF_FEATURES_FOR_ANY_PHASE_RULES_OR_SPEC_BASED_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES = 2 ** NUMB_OF_FEATURES_FOR_ANY_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_PURE_PHASE_RULES = 2 ** NUMB_OF_FEATURES_FOR_PURE_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_SYMBOLIC_EXECUTION_PHASE_RULES = \
        2 ** NUMB_OF_FEATURES_FOR_SYMBOLIC_EXECUTION_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_PHASE_RULES = 2 ** NUMB_OF_FEATURES_FOR_UNFOLDING_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATORS_FOR_SKETCH_HOL_RULES = 2 ** NUMB_OF_FEATURES_FOR_SKETCH_HOL_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_1 = 2 ** NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES_1
    NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_2 = 2 ** NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES_2
    NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_3 = 2 ** NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES_3
    NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_4 = 2 ** NUMB_OF_FEATURES_FOR_CALL_ABDUCTION_RULES_4
    NUMB_OF_FEATURE_COMBINATIONS_FOR_POST_BLOCK_PHASE_RULES = 2 ** NUMB_OF_FEATURES_FOR_POST_BLOCK_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_POINTER_PHASE_RULES = 2 ** NUMB_OF_FEATURES_FOR_POINTER_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_POST_PHASE_RULES = 2 ** NUMB_OF_FEATURES_FOR_UNFOLDING_POST_PHASE_RULES
    NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_NO_UNFOLD_PHASE_RULES = \
        2 ** NUMB_OF_FEATURES_FOR_UNFOLDING_NO_UNFOLD_PHASE_RULES


def json_overall_result(overall_results):
    return {
        "overall_result": overall_results
    }


class Individual(list):
    """This class describes SuSLik's search strategy for individuals in each generation of each group."""

    def __init__(self,
                 group_id,  # group_id = 0 corresponds to initial group created by mutating the manually tuned one.
                 generation_id,
                 individual_id,
                 rank=999999,
                 runtime_rule_order_selection=True,  # a.k.a dynamic optimisation
                 fewer_feature_combinations=True,
                 only_order_no_weight=False,
                 nan=100,
                 time=9999999999.0,
                 backtracking=9999999999,
                 rules=9999999999,
                 ancestors=None,
                 ancestor_ranks=None,
                 orders_of_any_phase_rules=None,
                 weights_of_any_phase_rules=None,
                 orders_of_pure_phase_rules=None,
                 weights_of_pure_phase_rules=None,
                 orders_of_symbolic_execution_rules=None,
                 weights_of_symbolic_execution_rules=None,
                 orders_of_unfolding_phase_rules=None,
                 weights_of_unfolding_phase_rules=None,
                 orders_of_any_phase_rules_or_spec_based_rules=None,
                 orders_of_sketch_hole_rules=None,
                 weights_of_sketch_hole_rules=None,
                 orders_of_pointer_phase_rules=None,
                 weights_of_pointer_phase_rules=None,
                 orders_of_post_block_phase_rules=None,
                 weights_of_post_block_phase_rules=None,
                 orders_of_call_abduction_rules_1=None,
                 weights_of_call_abduction_rules_1=None,
                 orders_of_call_abduction_rules_2=None,
                 weights_of_call_abduction_rules_2=None,
                 orders_of_call_abduction_rules_3=None,
                 weights_of_call_abduction_rules_3=None,
                 orders_of_call_abduction_rules_4=None,
                 weights_of_call_abduction_rules_4=None,
                 orders_of_unfolding_post_phase_rules=None,
                 weights_of_unfolding_post_phase_rules=None,
                 orders_of_unfolding_no_unfold_phase_rules=None,
                 weights_of_unfolding_no_unfold_phase_rules=None,
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
        self.runtime_rule_order_selection = runtime_rule_order_selection
        self.fewer_feature_combinations = fewer_feature_combinations
        self.only_order_no_weight = only_order_no_weight
        self.nan = nan
        self.time = time
        self.backtracking = backtracking
        self.rules = rules
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

        if weights_of_any_phase_rules is None:
            weights_of_any_phase_rules = []
            for feature_combination_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_ANY_PHASE_RULE):
                    ws_for_each_combination.append(1.0)
                weights_of_any_phase_rules.append(ws_for_each_combination)
            self.weights_of_any_phase_rules = weights_of_any_phase_rules

        if orders_of_pure_phase_rules is None:
            orders_of_pure_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_PURE_PHASE_RULES):
                orders_of_pure_phase_rules.append \
                    (random.sample(range(NUMB_OF_PURE_PHASE_RULE), NUMB_OF_PURE_PHASE_RULE))
            self.orders_of_pure_phase_rules = orders_of_pure_phase_rules

        if weights_of_pure_phase_rules is None:
            weights_of_pure_phase_rules = []
            for feature_combination_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_PURE_PHASE_RULES):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_PURE_PHASE_RULE):
                    ws_for_each_combination.append(1.0)
                weights_of_pure_phase_rules.append(ws_for_each_combination)
            self.weights_of_pure_phase_rules = weights_of_pure_phase_rules

        if orders_of_symbolic_execution_rules is None:
            orders_of_symbolic_execution_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_symbolic_execution_rules.append \
                    (random.sample(range(NUMB_OF_SYMBOLIC_EXECUTION_RULE), NUMB_OF_SYMBOLIC_EXECUTION_RULE))
        self.orders_of_symbolic_execution_rules = orders_of_symbolic_execution_rules

        if weights_of_symbolic_execution_rules is None:
            weights_of_symbolic_execution_rules = []
            for feature_combination_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_SYMBOLIC_EXECUTION_PHASE_RULES):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_SYMBOLIC_EXECUTION_RULE):
                    ws_for_each_combination.append(1.0)
                weights_of_symbolic_execution_rules.append(ws_for_each_combination)
            self.weights_of_symbolic_execution_rules = weights_of_symbolic_execution_rules

        if orders_of_unfolding_phase_rules is None:
            orders_of_unfolding_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_PHASE_RULES):
                orders_of_unfolding_phase_rules.append \
                    (random.sample(range(NUMB_OF_UNFOLDING_PHASE_RULE), NUMB_OF_UNFOLDING_PHASE_RULE))
            self.orders_of_unfolding_phase_rules = orders_of_unfolding_phase_rules

        if weights_of_unfolding_phase_rules is None:
            weights_of_unfolding_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_PHASE_RULES):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_UNFOLDING_PHASE_RULE):
                    ws_for_each_combination.append(1.0)
                weights_of_unfolding_phase_rules.append(ws_for_each_combination)
            self.weights_of_unfolding_phase_rules = weights_of_unfolding_phase_rules

        if orders_of_any_phase_rules_or_spec_based_rules is None:
            orders_of_any_phase_rules_or_spec_based_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES_OR_SPEC_BASED_RULES):
                orders_of_any_phase_rules_or_spec_based_rules.append \
                    (random.sample(range(NUMB_OF_ANY_PHASE_RULE_OR_SPEC_BASED_RULE),
                                   NUMB_OF_ANY_PHASE_RULE_OR_SPEC_BASED_RULE))
            self.orders_of_any_phase_rules_or_spec_based_rules = orders_of_any_phase_rules_or_spec_based_rules

        if orders_of_sketch_hole_rules is None:
            orders_of_sketch_hole_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATORS_FOR_SKETCH_HOL_RULES):
                orders_of_sketch_hole_rules.append(
                    random.sample(range(NUMB_OF_SKETCH_HOLE_RULE), NUMB_OF_SKETCH_HOLE_RULE))
            self.orders_of_sketch_hole_rules = orders_of_sketch_hole_rules

        if weights_of_sketch_hole_rules is None:
            weights_of_sketch_hole_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATORS_FOR_SKETCH_HOL_RULES):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_SKETCH_HOLE_RULE):
                    ws_for_each_combination.append(1.0)
                weights_of_sketch_hole_rules.append(ws_for_each_combination)
            self.weights_of_sketch_hole_rules = weights_of_sketch_hole_rules

        if orders_of_pointer_phase_rules is None:
            orders_of_pointer_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_POINTER_PHASE_RULES):
                orders_of_pointer_phase_rules.append \
                    (random.sample(range(NUMB_OF_POINTER_PHASE_RULE), NUMB_OF_POINTER_PHASE_RULE))
            self.orders_of_pointer_phase_rules = orders_of_pointer_phase_rules

        if weights_of_pointer_phase_rules is None:
            weights_of_pointer_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_POINTER_PHASE_RULES):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_POINTER_PHASE_RULE):
                    ws_for_each_combination.append(1.0)
                weights_of_pointer_phase_rules.append(ws_for_each_combination)
            self.weights_of_pointer_phase_rules = weights_of_pointer_phase_rules

        if orders_of_post_block_phase_rules is None:
            orders_of_post_block_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_POST_BLOCK_PHASE_RULES):
                orders_of_post_block_phase_rules.append \
                    (random.sample(range(NUMB_OF_POST_BLOCK_PHASE_RULE), NUMB_OF_POST_BLOCK_PHASE_RULE))
            self.orders_of_post_block_phase_rules = orders_of_post_block_phase_rules

        if weights_of_post_block_phase_rules is None:
            weights_of_post_block_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_POST_BLOCK_PHASE_RULES):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_POST_BLOCK_PHASE_RULE):
                    ws_for_each_combination.append(1.0)
                weights_of_post_block_phase_rules.append(ws_for_each_combination)
            self.weights_of_post_block_phase_rules = weights_of_post_block_phase_rules

        if orders_of_call_abduction_rules_1 is None:
            orders_of_call_abduction_rules_1 = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_1):
                orders_of_call_abduction_rules_1.append \
                    (random.sample(range(NUMB_OF_CALL_ABDUCTION_RULE_1), NUMB_OF_CALL_ABDUCTION_RULE_1))
            self.orders_of_call_abduction_rules_1 = orders_of_call_abduction_rules_1

        if weights_of_call_abduction_rules_1 is None:
            weights_of_call_abduction_rules_1 = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_1):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_CALL_ABDUCTION_RULE_1):
                    ws_for_each_combination.append(1.0)
                weights_of_call_abduction_rules_1.append(ws_for_each_combination)
            self.weights_of_call_abduction_rules_1 = weights_of_call_abduction_rules_1

        if orders_of_call_abduction_rules_2 is None:
            orders_of_call_abduction_rules_2 = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_2):
                orders_of_call_abduction_rules_2.append \
                    (random.sample(range(NUMB_OF_CALL_ABDUCTION_RULE_2), NUMB_OF_CALL_ABDUCTION_RULE_2))
            self.orders_of_call_abduction_rules_2 = orders_of_call_abduction_rules_2

        if weights_of_call_abduction_rules_2 is None:
            weights_of_call_abduction_rules_2 = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_2):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_CALL_ABDUCTION_RULE_2):
                    ws_for_each_combination.append(1.0)
                weights_of_call_abduction_rules_2.append(ws_for_each_combination)
            self.weights_of_call_abduction_rules_2 = weights_of_call_abduction_rules_2

        if orders_of_call_abduction_rules_3 is None:
            orders_of_call_abduction_rules_3 = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_3):
                orders_of_call_abduction_rules_3.append \
                    (random.sample(range(NUMB_OF_CALL_ABDUCTION_RULE_3), NUMB_OF_CALL_ABDUCTION_RULE_3))
            self.orders_of_call_abduction_rules_3 = orders_of_call_abduction_rules_3

        if weights_of_call_abduction_rules_3 is None:
            weights_of_call_abduction_rules_3 = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_3):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_CALL_ABDUCTION_RULE_3):
                    ws_for_each_combination.append(1.0)
                weights_of_call_abduction_rules_3.append(ws_for_each_combination)
            self.weights_of_call_abduction_rules_3 = weights_of_call_abduction_rules_3

        if orders_of_call_abduction_rules_4 is None:
            orders_of_call_abduction_rules_4 = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_4):
                orders_of_call_abduction_rules_4.append \
                    (random.sample(range(NUMB_OF_CALL_ABDUCTION_RULE_4), NUMB_OF_CALL_ABDUCTION_RULE_4))
            self.orders_of_call_abduction_rules_4 = orders_of_call_abduction_rules_4

        if weights_of_call_abduction_rules_4 is None:
            weights_of_call_abduction_rules_4 = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_4):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_CALL_ABDUCTION_RULE_4):
                    ws_for_each_combination.append(1.0)
                weights_of_call_abduction_rules_4.append(ws_for_each_combination)
            self.weights_of_call_abduction_rules_4 = weights_of_call_abduction_rules_4

        if orders_of_unfolding_post_phase_rules is None:
            orders_of_unfolding_post_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_POST_PHASE_RULES):
                orders_of_unfolding_post_phase_rules.append \
                    (random.sample(range(NUMB_OF_UNFOLDING_POST_PHASE_RULE), NUMB_OF_UNFOLDING_POST_PHASE_RULE))
            self.orders_of_unfolding_post_phase_rules = orders_of_unfolding_post_phase_rules

        if weights_of_unfolding_post_phase_rules is None:
            weights_of_unfolding_post_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_POST_PHASE_RULES):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_UNFOLDING_POST_PHASE_RULE):
                    ws_for_each_combination.append(1.0)
                weights_of_unfolding_post_phase_rules.append(ws_for_each_combination)
            self.weights_of_unfolding_post_phase_rules = weights_of_unfolding_post_phase_rules

        if orders_of_unfolding_no_unfold_phase_rules is None:
            orders_of_unfolding_no_unfold_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATION):
                orders_of_unfolding_no_unfold_phase_rules.append \
                    (random.sample(range(NUMB_OF_UNFOLDING_NO_UNFOLD_PHASE_RULES),
                                   NUMB_OF_UNFOLDING_NO_UNFOLD_PHASE_RULES))
            self.orders_of_unfolding_no_unfold_phase_rules = orders_of_unfolding_no_unfold_phase_rules

        if weights_of_unfolding_no_unfold_phase_rules is None:
            weights_of_unfolding_no_unfold_phase_rules = []
            for i in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_NO_UNFOLD_PHASE_RULES):
                ws_for_each_combination = []
                for rule_index in range(NUMB_OF_UNFOLDING_NO_UNFOLD_PHASE_RULES):
                    ws_for_each_combination.append(1.0)
                weights_of_unfolding_no_unfold_phase_rules.append(ws_for_each_combination)
            self.weights_of_unfolding_no_unfold_phase_rules = weights_of_unfolding_no_unfold_phase_rules

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

    def set_runtime_rule_order_selection(self, runtime_rule_order_selection):
        self.runtime_rule_order_selection = runtime_rule_order_selection

    def set_fewer_feature_combinations(self, fewer_feature_combinations):
        self.fewer_feature_combinations = fewer_feature_combinations

    def set_only_order_no_weight(self, only_order_no_weight):
        self.only_order_no_weight = only_order_no_weight

    def get_time(self):
        return self.time

    def get_backtracking(self):
        return self.backtracking

    def get_nan(self):
        return self.nan

    def get_rules(self):
        return self.rules

    def set_time(self, time):
        self.time = time

    def set_backtracking(self, backtracking):
        self.backtracking = backtracking

    def set_nan(self, nan):
        self.nan = nan

    def update_ancestor_with_current_individual_id(self):
        self.ancestors.append(self.individual_id)

    def update_ancestor_ranks_with_current_rank(self):
        self.ancestor_ranks.append(self.rank)

    def mutate(self):
        for order_of_any_phase_rules in self.orders_of_any_phase_rules:
            tools.mutShuffleIndexes(order_of_any_phase_rules, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES):
                for rule_index in range(NUMB_OF_ANY_PHASE_RULE):
                    weight = self.weights_of_any_phase_rules[feature_index][rule_index]
                    self.weights_of_any_phase_rules[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        for order_of_pure_phase_rules in self.orders_of_pure_phase_rules:
            tools.mutShuffleIndexes(order_of_pure_phase_rules, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_PURE_PHASE_RULES):
                for rule_index in range(NUMB_OF_PURE_PHASE_RULE):
                    weight = self.weights_of_pure_phase_rules[feature_index][rule_index]
                    self.weights_of_pure_phase_rules[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        for order_of_symbolic_execution_rules in self.orders_of_symbolic_execution_rules:
            tools.mutShuffleIndexes(order_of_symbolic_execution_rules, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURES_FOR_SYMBOLIC_EXECUTION_PHASE_RULES):
                for rule_index in range(NUMB_OF_SYMBOLIC_EXECUTION_RULE):
                    weight = self.weights_of_symbolic_execution_rules[feature_index][rule_index]
                    self.weights_of_symbolic_execution_rules[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        for order_of_unfolding_phase_rules in self.orders_of_unfolding_phase_rules:
            tools.mutShuffleIndexes(order_of_unfolding_phase_rules, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_PHASE_RULES):
                for rule_index in range(NUMB_OF_UNFOLDING_PHASE_RULE):
                    weight = self.weights_of_unfolding_phase_rules[feature_index][rule_index]
                    self.weights_of_unfolding_phase_rules[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        for order_of_any_phase_rules_or_spec_based_rules in self.orders_of_any_phase_rules_or_spec_based_rules:
            tools.mutShuffleIndexes(order_of_any_phase_rules_or_spec_based_rules, indpb=INDPB)

        for order_of_sketch_hole in self.orders_of_sketch_hole_rules:
            tools.mutShuffleIndexes(order_of_sketch_hole, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURE_COMBINATORS_FOR_SKETCH_HOL_RULES):
                for rule_index in range(NUMB_OF_SKETCH_HOLE_RULE):
                    weight = self.weights_of_sketch_hole_rules[feature_index][rule_index]
                    self.weights_of_sketch_hole_rules[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        for order_of_pointer_phase_rules in self.orders_of_pointer_phase_rules:
            tools.mutShuffleIndexes(order_of_pointer_phase_rules, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_POINTER_PHASE_RULES):
                for rule_index in range(NUMB_OF_POINTER_PHASE_RULE):
                    weight = self.weights_of_pointer_phase_rules[feature_index][rule_index]
                    self.weights_of_pointer_phase_rules[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        for order_of_post_block_phase_rule in self.orders_of_post_block_phase_rules:
            tools.mutShuffleIndexes(order_of_post_block_phase_rule, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_POST_BLOCK_PHASE_RULES):
                for rule_index in range(NUMB_OF_POST_BLOCK_PHASE_RULE):
                    weight = self.weights_of_post_block_phase_rules[feature_index][rule_index]
                    self.weights_of_post_block_phase_rules[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        for order_of_call_abduction_rules_1 in self.orders_of_call_abduction_rules_1:
            tools.mutShuffleIndexes(order_of_call_abduction_rules_1, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_1):
                for rule_index in range(NUMB_OF_CALL_ABDUCTION_RULE_1):
                    weight = self.weights_of_call_abduction_rules_1[feature_index][rule_index]
                    self.weights_of_call_abduction_rules_1[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        for order_of_call_abduction_rules_2 in self.orders_of_call_abduction_rules_2:
            tools.mutShuffleIndexes(order_of_call_abduction_rules_2, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_2):
                for rule_index in range(NUMB_OF_CALL_ABDUCTION_RULE_2):
                    weight = self.weights_of_call_abduction_rules_2[feature_index][rule_index]
                    self.weights_of_call_abduction_rules_2[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        for order_of_call_abduction_rules_3 in self.orders_of_call_abduction_rules_3:
            tools.mutShuffleIndexes(order_of_call_abduction_rules_3, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_3):
                for rule_index in range(NUMB_OF_CALL_ABDUCTION_RULE_3):
                    weight = self.weights_of_call_abduction_rules_3[feature_index][rule_index]
                    self.weights_of_call_abduction_rules_3[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        for order_of_call_abduction_rules_4 in self.orders_of_call_abduction_rules_4:
            tools.mutShuffleIndexes(order_of_call_abduction_rules_4, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_4):
                for rule_index in range(NUMB_OF_CALL_ABDUCTION_RULE_4):
                    weight = self.weights_of_call_abduction_rules_4[feature_index][rule_index]
                    self.weights_of_call_abduction_rules_4[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        for order_of_unfolding_post_phase_rules in self.orders_of_unfolding_post_phase_rules:
            tools.mutShuffleIndexes(order_of_unfolding_post_phase_rules, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_POST_PHASE_RULES):
                for rule_index in range(NUMB_OF_UNFOLDING_POST_PHASE_RULE):
                    weight = self.weights_of_unfolding_post_phase_rules[feature_index][rule_index]
                    self.weights_of_unfolding_post_phase_rules[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        for order_of_unfolding_no_unfold_phase_rules in self.orders_of_unfolding_no_unfold_phase_rules:
            tools.mutShuffleIndexes(order_of_unfolding_no_unfold_phase_rules, indpb=INDPB)
        if not self.only_order_no_weight:
            for feature_index in range(NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_NO_UNFOLD_PHASE_RULES):
                for rule_index in range(NUMB_OF_UNFOLDING_NO_UNFOLD_PHASE_RULES):
                    weight = self.weights_of_unfolding_no_unfold_phase_rules[feature_index][rule_index]
                    self.weights_of_unfolding_no_unfold_phase_rules[feature_index][rule_index] = \
                        weight * random.normalvariate(1.0, STANDARD_DEVIATION)

        self.weight_of_cost_no_call_goal_pre = self.weight_of_cost_call_goal_pre * weight * random.normalvariate(1.0, STANDARD_DEVIATION)
        self.weight_of_cost_no_call_goal_post = self.weight_of_cost_call_goal_post * weight * random.normalvariate(1.0, STANDARD_DEVIATION)
        self.weight_of_cost_call_goal = self.weight_of_cost_call_goal * weight * random.normalvariate(1.0, STANDARD_DEVIATION)
        self.weight_of_cost_call_goal_pre = self.weight_of_cost_call_goal_pre * weight * random.normalvariate(1.0, STANDARD_DEVIATION)
        self.weight_of_cost_call_goal_post = self.weight_of_cost_call_goal_post * weight * random.normalvariate(1.0, STANDARD_DEVIATION)

    # TODO: This only supports the static optimisation. (compiler-time optimisation)
    def default(self):

        orders_of_any_phase_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES)):
            orders_of_any_phase_rules.append(list(range(NUMB_OF_ANY_PHASE_RULE)))
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
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_ANY_PHASE_RULES_OR_SPEC_BASED_RULES)):
            orders_of_any_phase_rules_or_spec_based_rules.append(
                list(range(0, NUMB_OF_ANY_PHASE_RULE_OR_SPEC_BASED_RULE)))
        self.orders_of_any_phase_rules_or_spec_based_rules = orders_of_any_phase_rules_or_spec_based_rules

        orders_of_sketch_hole_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATION)):
            orders_of_sketch_hole_rules.append(list(range(0, NUMB_OF_SKETCH_HOLE_RULE)))
        self.orders_of_sketch_hole_rules = orders_of_sketch_hole_rules

        orders_of_pointer_phase_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_POINTER_PHASE_RULES)):
            orders_of_pointer_phase_rules.append(list(range(0, NUMB_OF_POINTER_PHASE_RULE)))
        self.orders_of_pointer_phase_rules = orders_of_pointer_phase_rules

        orders_of_post_block_phase_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_POST_BLOCK_PHASE_RULES)):
            orders_of_post_block_phase_rules.append(list(range(0, NUMB_OF_POST_BLOCK_PHASE_RULE)))
        self.orders_of_post_block_phase_rules = orders_of_post_block_phase_rules

        orders_of_call_abduction_rules_1 = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_1)):
            orders_of_call_abduction_rules_1.append(list(range(0, NUMB_OF_CALL_ABDUCTION_RULE_1)))
        self.orders_of_call_abduction_rules_1 = orders_of_call_abduction_rules_1

        orders_of_call_abduction_rules_2 = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_2)):
            orders_of_call_abduction_rules_2.append(list(range(0, NUMB_OF_CALL_ABDUCTION_RULE_2)))
        self.orders_of_call_abduction_rules_2 = orders_of_call_abduction_rules_2

        orders_of_call_abduction_rules_3 = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_3)):
            orders_of_call_abduction_rules_3.append(list(range(0, NUMB_OF_CALL_ABDUCTION_RULE_3)))
        self.orders_of_call_abduction_rules_3 = orders_of_call_abduction_rules_3

        orders_of_call_abduction_rules_4 = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_CALL_ABDUCTION_RULES_4)):
            orders_of_call_abduction_rules_4.append(list(range(0, NUMB_OF_CALL_ABDUCTION_RULE_4)))
        self.orders_of_call_abduction_rules_4 = orders_of_call_abduction_rules_4

        orders_of_unfolding_post_phase_rules = []
        for i in list(range(NUMB_OF_FEATURE_COMBINATIONS_FOR_UNFOLDING_POST_PHASE_RULES)):
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

    def json_search_parameter_file_path(self):
        json_file_name = "search_parameter" + "_" + str(self.group_id) + "_" + str(self.generation_id) + "_" + \
                         str(self.individual_id) + ".json"
        path = PATH_TO_TACTICS + json_file_name
        return path

    def write_json_parameter_file(self):

        json_data_to_write = {
            "runtime_rule_order_selection": self.runtime_rule_order_selection,
            "fewer_feature_combinations": self.fewer_feature_combinations,
            "only_order_no_weight": self.only_order_no_weight,
            "orders_of_any_phase_rules": self.orders_of_any_phase_rules,
            "weights_of_any_phase_rules": self.weights_of_any_phase_rules,
            "orders_of_pure_phase_rules": self.orders_of_pure_phase_rules,
            "weights_of_pure_phase_rules": self.weights_of_pure_phase_rules,
            "orders_of_symbolic_execution_rules": self.orders_of_symbolic_execution_rules,
            "weights_of_symbolic_execution_rules": self.weights_of_symbolic_execution_rules,
            "orders_of_unfolding_phase_rules": self.orders_of_unfolding_phase_rules,
            "weights_of_unfolding_phase_rules": self.weights_of_unfolding_phase_rules,
            "orders_of_any_phase_rules_or_spec_based_rules": self.orders_of_any_phase_rules_or_spec_based_rules,
            "orders_of_sketch_hole_rules": self.orders_of_sketch_hole_rules,
            "weights_of_sketch_hole_rules": self.weights_of_sketch_hole_rules,
            "orders_of_pointer_phase_rules": self.orders_of_pointer_phase_rules,
            "weights_of_pointer_phase_rules": self.weights_of_pointer_phase_rules,
            "orders_of_post_block_phase_rules": self.orders_of_post_block_phase_rules,
            "weights_of_post_block_phase_rules": self.weights_of_post_block_phase_rules,
            "orders_of_call_abduction_rules_1": self.orders_of_call_abduction_rules_1,
            "weights_of_call_abduction_rules_1": self.weights_of_call_abduction_rules_1,
            "orders_of_call_abduction_rules_2": self.orders_of_call_abduction_rules_2,
            "weights_of_call_abduction_rules_2": self.weights_of_call_abduction_rules_2,
            "orders_of_call_abduction_rules_3": self.orders_of_call_abduction_rules_3,
            "weights_of_call_abduction_rules_3": self.weights_of_call_abduction_rules_3,
            "orders_of_call_abduction_rules_4": self.orders_of_call_abduction_rules_4,
            "weights_of_call_abduction_rules_4": self.weights_of_call_abduction_rules_4,
            "orders_of_unfolding_post_phase_rules": self.orders_of_unfolding_post_phase_rules,
            "weights_of_unfolding_post_phase_rules": self.weights_of_unfolding_post_phase_rules,
            "orders_of_unfolding_no_unfold_phase_rules": self.orders_of_unfolding_no_unfold_phase_rules,
            "weights_of_unfolding_no_unfold_phase_rules": self.weights_of_unfolding_no_unfold_phase_rules,
            "weight_of_cost_no_call_goal_pre": self.weight_of_cost_no_call_goal_pre,
            "weight_of_cost_no_call_goal_post": self.weight_of_cost_no_call_goal_post,
            "weight_of_cost_call_goal": self.weight_of_cost_call_goal,
            "weight_of_cost_call_goal_pre": self.weight_of_cost_call_goal_pre,
            "weight_of_cost_call_goal_post": self.weight_of_cost_call_goal_post
        }

        with open(self.json_search_parameter_file_path(), 'w') as new_json_file_to_write:
            json.dump(json_data_to_write, new_json_file_to_write, indent=2)

    def csv_result_file_path(self, is_for_training=True):

        if is_for_training:
            result_type = "_training_"
        else:
            result_type = "_validation_"

        path = roboevaluation.EVAL_FOLDER + '/stats-performance' + result_type + str(self.group_id) + "_" \
               + str(self.generation_id) + '_' + str(self.individual_id) + '.csv'
        return path

    def evaluate(self, for_training=True):

        if for_training:
            data = roboevaluation.TRAINING_DATA
        else:
            data = roboevaluation.VALIDATION_DATA

        results1 = roboevaluation.evaluate_n_times(
            1, roboevaluation.METACONFIG1, roboevaluation.CONFIG1, data,
            roboevaluation.RESULTS1, roboevaluation.CSV_IN, roboevaluation.CSV_TEMP, True,
            self.group_id, self.generation_id, self.individual_id)

        roboevaluation.write_stats1(roboevaluation.METACONFIG1, roboevaluation.CONFIG1, data,
                                    results1, self.csv_result_file_path(is_for_training=for_training))

        df = pandas.read_csv(filepath_or_buffer=self.csv_result_file_path(is_for_training=for_training), na_values=['FAIL', '-'])

        number_of_nans = int(df['Time(mut)'].isna().sum())
        total_time = df['Time(mut)'].sum()
        total_backtracking = int(df['Backtrackings(mut)'].isna().sum())

        times = df['Time(mut)']
        df_rules = df['Rules(mut)']

        pairs_of_times_and_rules = list(zip(times, df_rules))

        def sum_non_nan_rules(pairs):
            temp_total_numb_of_fired_rules = 0
            for first, second in pairs:
                if not (math.isnan(first)):
                    temp_total_numb_of_fired_rules = temp_total_numb_of_fired_rules + second
                else:
                    temp_total_numb_of_fired_rules
            return temp_total_numb_of_fired_rules

        total_numb_of_fired_rules = sum_non_nan_rules(pairs_of_times_and_rules)

        self.nan, self.time, self.backtracking, self.rules = \
            (number_of_nans, total_time, total_backtracking, total_numb_of_fired_rules)

        return number_of_nans, total_time, total_backtracking, total_numb_of_fired_rules

    # Note that we use the rank of individual in the file name.
    def json_result_file_path(self, is_for_training=True):

        if is_for_training:
            result_type = "_training_"
        else:
            result_type = "_validation_"

        return "robo-evaluation-utils/result" + result_type + str(self.group_id) + "_" + str(self.generation_id) + "_" \
               + str(self.rank) + ".json"

    def json_tentative_overall_result_file_path(self, is_for_training=True):

        if is_for_training:
            result_type = "_tentative_overall_training_"
        else:
            result_type = "_tentative_overall_validation_"

        return "robo-evaluation-utils/result" + result_type + str(self.group_id) + ".json"

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
            "fired_rules": self.rules,
            "search_time": self.time,
            "backtracking": self.backtracking,
            "ancestors": self.ancestors,
            "ancestor_ranks": self.ancestor_ranks,
            "is_for_training": is_for_training,
            "population_size": POPULATION_SIZE,
            "independent_probability": INDPB,
            "timeout": roboevaluation.TIMEOUT,
            "standard_deviation_for_weights": STANDARD_DEVIATION,
            "runtime_rule_order_selection": self.runtime_rule_order_selection,
            "fewer_feature_combinations": self.fewer_feature_combinations,
            "only_order_no_weight": self.only_order_no_weight
        }

    def write_json_result(self, for_training=True):

        with open(self.json_result_file_path(for_training), 'w') as json_result_file_to_write:
            json.dump(self.json_result(for_training), json_result_file_to_write, indent=2)

    def write_tentative_overall_json_result(self, for_training=True):
        with open(self.json_tentative_overall_result_file_path(for_training), 'a') as \
                json_overall_validation_result_file_to_write:
            json.dump(self.json_result(for_training), json_overall_validation_result_file_to_write)
            json_overall_validation_result_file_to_write.write("\n")
            json_overall_validation_result_file_to_write.close()

    def write_overall_json_result(self, overall_results, for_training=True):
        with open(self.json_overall_result_file_path(for_training), 'w') as json_result_file_to_write:
            json.dump(json_overall_result(overall_results), json_result_file_to_write, indent=2)


def get_total_time(individual: Individual):
    return individual.get_time()


def get_total_backtracking(individual: Individual):
    return individual.get_backtracking()


def get_total_rules(individual: Individual):
    return individual.get_rules()


def get_number_of_nans(individual: Individual):
    return individual.get_nan()


class Group(list):
    """This class describes a group of SuSLik instances."""

    def __init__(self,
                 start_at_tuned_order: bool,
                 runtime_selection: bool,
                 fewer_feature_comb: bool,
                 only_order_no_weight: bool,
                 group_id: int = 0,
                 individuals: List[Individual] = None,
                 overall_json_training_result = None,
                 overall_json_validation_result = None):
        super().__init__()
        self.start_at_tuned_order = start_at_tuned_order
        self.runtime_selection = runtime_selection
        self.fewer_feature_comb = fewer_feature_comb
        self.only_order_no_weight = only_order_no_weight
        self.group_id = group_id
        if individuals is None:
            self.individuals = []
        if overall_json_training_result is None:
            self.overall_json_training_result = []
        if overall_json_validation_result is None:
            self.overall_json_validation_result = []

    def mk_initial_population_and_evaluate(self):
        for individual_id in list(range(0, POPULATION_SIZE)):
            new_individual = Individual(group_id=self.group_id,
                                        generation_id=0,
                                        individual_id=individual_id,
                                        runtime_rule_order_selection=self.runtime_selection,
                                        fewer_feature_combinations=self.fewer_feature_comb,
                                        only_order_no_weight=self.only_order_no_weight
                                        )
            if self.start_at_tuned_order:
                new_individual.default()
                if individual_id != 0:
                    new_individual.mutate()
            new_individual.write_json_parameter_file()
            new_individual.evaluate(for_training=True)
            self.individuals.append(new_individual)

    def set_generation_id(self, generation_id):
        for individual in self.individuals:
            individual.set_generation_id(generation_id=generation_id)

    def change_old_generation_to_new_generation_and_evaluate_new_individuals_for_training(self, new_generation_id):
        # assume the individuals are already sorted.
        survivors_of_old_generation = self.individuals[:POPULATION_SIZE]

        # firstly update ancestors using the current individual_id
        for individual in survivors_of_old_generation:
            individual.update_ancestor_with_current_individual_id()
            individual.update_ancestor_ranks_with_current_rank()

        # secondly update individual_id and generation_id of survivors_of_old_generation
        individual_id = 0
        for individual in survivors_of_old_generation:
            individual.set_generation_id(new_generation_id)
            individual.set_individual_id(individual_id)
            individual.write_json_parameter_file()
            # We should evaluate these individuals once again even though doing so is repetitive:
            # we want to eliminate the performance effect caused by short-term OS background situations.
            individual.evaluate(for_training=True)
            individual_id = individual_id + 1

        # mutants are to be mutated
        mutants = copy.deepcopy(survivors_of_old_generation) + copy.deepcopy(survivors_of_old_generation[:2])

        for individual in mutants:
            individual.mutate()
            individual.set_individual_id(individual_id)
            individual_id = individual_id + 1
            individual.write_json_parameter_file()
            individual.evaluate(for_training=True)

        self.individuals = survivors_of_old_generation + mutants

    def sort_rank_individuals_then_validate_the_best(self):
        self.individuals.sort(key=get_total_rules)
        self.individuals.sort(key=get_number_of_nans)
        rank = 0
        for individual in self.individuals:
            individual.set_rank(rank)
            rank = rank + 1
            individual.write_json_result(for_training=True)
        self.individuals[0].write_tentative_overall_json_result(for_training=True)
        self.overall_json_training_result.append(self.individuals[0].json_result(is_for_training=True))
        # validation
        best_individual = copy.deepcopy(self.individuals[0])
        best_individual.evaluate(for_training=False)
        best_individual.write_json_result(for_training=False)
        best_individual.write_tentative_overall_json_result(for_training=False)
        self.overall_json_validation_result.append(best_individual.json_result(is_for_training=False))


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

    # create initial groups
    group_static_random_order = Group(
        start_at_tuned_order=False,
        runtime_selection=False,
        fewer_feature_comb=FEWER_FEATURE_COMBINATION,
        only_order_no_weight=True,
        group_id=0
    )
    group_static_tuned_order = Group(
        start_at_tuned_order=True,
        runtime_selection=False,
        fewer_feature_comb=FEWER_FEATURE_COMBINATION,
        only_order_no_weight=True,
        group_id=1
    )
    group_static_weight = Group(
        start_at_tuned_order=True,
        runtime_selection=False,
        fewer_feature_comb=FEWER_FEATURE_COMBINATION,
        only_order_no_weight=False,
        group_id=2
    )
    group_dynamic_weight = Group(
        start_at_tuned_order=True,
        runtime_selection=True,
        fewer_feature_comb=FEWER_FEATURE_COMBINATION,
        only_order_no_weight=False,
        group_id=3
    )

    groups = [
        #group_static_random_order,
        #group_static_tuned_order,
        group_static_weight,
        group_dynamic_weight
    ]

    for group in groups:
        group.mk_initial_population_and_evaluate()
        group.sort_rank_individuals_then_validate_the_best()

    generation_id = 1

    # begin the evolution
    while generation_id <= MAXIMUM_NUMBER_OF_GENERATIONS:

        print("----- generation %i -----" % generation_id)

        for group in groups:
            group.change_old_generation_to_new_generation_and_evaluate_new_individuals_for_training\
                (new_generation_id=generation_id)
            group.sort_rank_individuals_then_validate_the_best()

        generation_id = generation_id + 1

    #
    for group in groups:
        final_winner = copy.deepcopy(group.individuals[0])
        final_winner.set_generation_id(generation_id=generation_id)
        final_winner.write_overall_json_result(group.overall_json_training_result)
        final_winner.write_overall_json_result(group.overall_json_validation_result)

    return 0


if __name__ == "__main__":
    main()
