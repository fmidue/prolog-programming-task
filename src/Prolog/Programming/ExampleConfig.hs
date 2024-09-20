{-# LANGUAGE QuasiQuotes #-}
module Prolog.Programming.ExampleConfig where

import Prolog.Programming.Data (Config(..))

import qualified Text.RawString.QQ as RS (r)

exampleConfig :: Config
exampleConfig = Config
  [RS.r|/* % comments for test cases have to start with an extra %
 * % timeout per test in ms (defaults to 10000, only the first timeout is used)
 * Global timeout: 10000
 * % style of derivation tree rendering can be either 'query' or 'resolution' (defaults to 'query')
 * Tree style: query
 * % The two include options control if and how the hidden definitions and definitions from the task description should be included into the submission.
 * % 'yes': include as is,
 * % 'filtered':
 * %    - For hidden definitions all clauses for predicate pred/k are filtered out if the input program also contains clauses for pred/k,
 * %    - For task definitions clauses that occur identically in the input program are filtered out
 * % 'no': do not include.
 * % Both default to yes
 * Include hidden definitions: [ yes | filtered ]
 * Include task definitions: [ yes | filtered | no ]
 * % allow/disallow the use of [H|T] matching on list values, defaults to 'yes' (experimental: might not recognize all instances of the pattern)
 * Allow list pattern matching: [ yes | no ]
 * % prefixing a test with [<time out in ms>] sets a local timeout for that test
 * a_predicate(Foo,Bar): a_predicate(expected_foo1,expected_bar1), a_predicate(expected_foo2,expected_bar2)
 * a_statement_that_has_to_be_true
 * !a_predicate_whose_answers_are_hidden(Foo,Bar): a_predicate(expected_foo1,expected_bar1), a_predicate(expected_foo2,expected_bar2)
 * !a_hidden_statement_that_has_to_be_true
 * !(<description>) a_hidden_statement_that_has_to_be_true_with_a_description_shown_on_failure
 * @a_test_with_resolution_tree(X) % Only shown if test fails.
 * -a_statement_that_has_to_be_false % also works for all other test statements given above
 * % when combining multiple flags the order has to be <timeout><negative><tree><hidden><space>*<test>
 * new a_predicate_to_define(X): predicate description
 *    % require the definition of a predicate with a user choosen name. Use a_predicate_to_define to refer this predicate in other tests.
 *    % New predicates will be mapped to required predicates in the order they are defined.
 *    % (The initial solution automatically provides comments helping the user with the correct ordering.)
 */
/* Everything from here on (up to an optional hidden section separated by a line of 3 or more dashes)
 * will be part of the visible exercise description (In other words: Only the first comment block is special).
 *
 * You can add as many tests as you like, but keep Autotool's time limit in mind. Additionally, every test has its own time limit,
 * so if one of your tests does not terminate (soon enough) this will be reported as a failure (mentioning the timeout).
 *
 * In this visible part, you can place the explanation of the exercise and all facts & clauses you want to give to the student.
 */
a_fact.
a_clause(Foo) :- a_clause(Foo).
a_dcg_rule --> a_dcg_rule, [terminal1, terminal2], { prolog_term }.
a_test_with_resolution_tree(left_branch) :- fail. % See test line 5
a_test_with_resolution_tree(right_branch) :- fail. % See test line 5
/*
 * The program text will be concatenated with whatever the student submits (subject to include settings).
 */
------------------------------
/*
 * This is also part of the program, but is not presented to the student.
 *
 * Be careful to avoid naming clashes to not confuse the student with error messages about code they can't see.
 * Clashes can be avoided by the 'filtered' include setting, but giving priority to the student's version of some
 * predicate can weaken the test suite.
 */
  |]
