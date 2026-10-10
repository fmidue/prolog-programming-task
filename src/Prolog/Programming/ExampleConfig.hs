{-# LANGUAGE QuasiQuotes #-}

module Prolog.Programming.ExampleConfig where

import Prolog.Programming.Data (Config)

import qualified Text.RawString.QQ as RS (r)

exampleConfig :: Config
exampleConfig =
  [RS.r|
# uses the last provided values if fields are provided multiple times

# timeout per test in ms (defaults to 10000)
globalTimeout: 1000

# style of derivation tree rendering can be either 'query' or 'resolution' (defaults to 'query')
treeStyle: query

# The two include options control if and how the hidden definitions and definitions from the task description should be included into the submission.
# 'yes': include as is,
# 'filtered':
#    - For hidden definitions all clauses for predicate pred/k are filtered out if the input program also contains clauses for pred/k,
#    - For task definitions clauses that occur identically in the input program are filtered out
# 'no': do not include (only available for includeTaskDefinitions).
# Both default to yes
# includeTaskDefinitions: yes
# includeHiddenDefinitions: yes

# whether to allow the use of [H|T] matching on list values, defaults to 'true' (experimental: might not recognize all instances of the pattern)
# allowListPatternMatching: true

# whether to enable display of button that allows students to transfer code to SWISH; disabled by default
# showSWISHButton: false

# prefixing a test with [<time out in ms>] sets a local timeout for that test
specifications:
  - 'a_predicate(Foo,Bar): a_predicate(expected_foo1,expected_bar1), a_predicate(expected_foo2,expected_bar2)'
  - 'a_statement_that_has_to_be_true'
  - '!a_predicate_whose_answers_are_hidden(Foo,Bar): a_predicate_whose_answers_are_hidden(expected_foo1,expected_bar1), a_predicate_whose_answers_are_hidden(expected_foo2,expected_bar2)'
  - '!a_hidden_statement_that_has_to_be_true'
  - '!(<description>) a_hidden_statement_that_has_to_be_true_with_a_description_shown_on_failure'
  - '@a_test_with_resolution_tree(X)' # only shown if test fails
  - '-a_statement_that_has_to_be_false' # also works for all other test statements given above
  # When combining multiple flags, the order has to be: <timeout><negative><tree><hidden><space>*<test>
  - 'new a_predicate_to_define(X): predicate description'
  # Require the definition of a predicate with a user chosen name. Use a_predicate_to_define to refer to this predicate in other tests.
  # New predicates will be mapped to required predicates in the order they are defined.
  # (The initial solution automatically provides comments helping the user with the correct ordering.)

# whether to run all tests and checks on the sample solution or not; enabled by default
rigorousValidation: true

# setting for code analysis;
# The status field for each aspect has the following possible values:
# 'ignore': aspect is ignored
# 'hint': detections are reported with severity hint
# 'warn': detections are reported with severity warn
# 'reject': programs with detections are rejected
# The default value for these fields is 'ignore' (in which case the aspect's mention can be omitted as well).
codeAnalysis:
  singletonVariables:
    # what to do concerning detection of singleton variables
    status: hint
  cutUsage:
    # what to do concerning detection of cut usage
    status: warn
    # additional message to display next to default feedback
    # additionalMessage: "We didn't introduce this operator yet."
    # This field is only allowed to appear when status is not set to 'ignore', and even otherwise it is optional.
  inconsistentArities:
    # what to do concerning detection of inconsistent arities
    status: warn
    # predicates to ignore for detection
    # useful when predicates provided by libraries can be used with different arities
    # ignorePredicates:
    #  - append # append/2 and append/3 are both provided by SWI-Prolog
    # This field is only allowed to appear when status is not set to 'ignore', and even otherwise it is optional.
  ungroupedDefinitions:
    # what to do concerning detection of ungrouped predicate definitions
    status: hint
  recursion:
    # what to do concerning detection of recursive predicates
    status: ignore
    # additional message to display next to default feedback
    # additionalMessage: "Recursion is not part of this exercise yet."
    # This field is only allowed to appear when status is not set to 'ignore', and even otherwise it is optional.
  inlining:
    # what to do concerning terms that can be inlined into the clause head
    status: hint

  # which predicates are not allowed to be used
  forbiddenPredicates:
   - not/1
   - \+/1
   - \=/2
   - \==/2
  # This field is optional and otherwise takes a list of predicate identities.

------------------------------
/* Everything in this section
 * will be part of the visible exercise description.
 *
 * You can add as many tests as you like, but keep Autotool's time limit in mind. Additionally, every test has its own time limit,
 * so if one of your tests does not terminate (soon enough) this will be reported as a failure (mentioning the timeout).
 *
 * In this visible part, you can place the explanation of the exercise and all facts & clauses you want to give to the student.
 */
a_fact.
a_clause(Foo) :- a_clause(Foo).
a_dcg_rule --> a_dcg_rule, [terminal1, terminal2], { prolog_term }.
a_test_with_resolution_tree(left_branch) :- fail.
a_test_with_resolution_tree(right_branch) :- fail.
/*
 * The program text will be concatenated with whatever the student submits (subject to include settings).
 */
------------------------------
/* This is the sample solution shown to students after deadline.
 * It is required and needs to be in the third section.
 *
 * The provided solution needs to pass all tests and checks specified in the first section of the config.
 * It will be verified on upload.
 */
p(_).
a_predicate(expected_foo1,expected_bar1).
a_predicate(expected_foo2,expected_bar2).
a_predicate_whose_answers_are_hidden(expected_foo1,expected_bar1).
a_predicate_whose_answers_are_hidden(expected_foo2,expected_bar2).
a_hidden_statement_that_has_to_be_true_with_a_description_shown_on_failure.

a_hidden_statement_that_has_to_be_true.
a_statement_that_has_to_be_false :- false.
a_statement_that_has_to_be_true.
a_test_with_resolution_tree(foo).
------------------------------
/* Anything that follows here is also part of the program, but is not presented to the student.
 * This section is optional.
 *
 * Be careful to avoid naming clashes to not confuse the student with error messages about code they can't see.
 * Clashes can be prevented by the 'filtered' include setting, but giving priority to the student's version of some
 * predicate can weaken the test suite.
 *
 * If a data constructor or constant begins with hidden__ then it will not be visible in feedback resulting from query tests.
 * The results containing these constructors/constants still need to appear in the list of expected results.
 * When the difference between the expected and actual query result contains only solutions with hidden data a special error message
 * informs the student that their submission is not general enough (in the sense that its rules do not work for arbitrary data).
 *
 * Note that derivation trees are currently not subject to filtering of hidden data!
 */
  |]
