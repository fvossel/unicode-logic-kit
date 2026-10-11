"""A quantified variable that stands inside a lambda term in argument position.

``∀x Pos(λy. R(x, y))`` says of every ``x`` that the property ``R(x, ·)`` is positive. A
route that reads an atom as a letter named by its written form takes the instance at
``alice`` as the letter ``Pos(λy. R(alice, y))`` and the one at ``bob`` as another. The
variable has to be replaced INSIDE the lambda term for that: left in place, both
instances are the one letter ``Pos(λy. R(x, y))``, and the quantifier ranges over
nothing.

The witness formula ``(∃x Pos(λy. R(x, y))) → (∀x Pos(λy. R(x, y)))`` is not valid over
two individuals: with the letter of ``alice`` true and that of ``bob`` false the
antecedent is true and the consequent false. With one letter for both it reads
``L → L``.
"""

import pytest

from unicode_logic_kit import MSFLParser, fuzzy_evaluate, fuzzy_is_valid, kleene_value
from unicode_logic_kit.fol.nodes import LukImplication
from unicode_logic_kit.semantics import LP_MATRIX, K3_MATRIX, manyvalued, matrix_is_valid, matrix_value
from unicode_logic_kit.semantics.fuzzy import ground_quantifiers

TO = MSFLParser(third_order=True)
D = {"alice", "bob"}

EVERY = TO.parse("∀x Pos(λy. R(x, y))")
WITNESS = TO.parse("(∃x Pos(λy. R(x, y))) → (∀x Pos(λy. R(x, y)))")
INSTANCES = {"Pos(λy. R(alice, y))": 1.0, "Pos(λy. R(bob, y))": 0.0}


def test_the_three_valued_evaluator_reads_one_letter_for_each_individual():
    assert kleene_value(EVERY, INSTANCES, domain=D) == 0.0
    assert kleene_value(TO.parse("∃x Pos(λy. R(x, y))"), INSTANCES, domain=D) == 1.0
    with pytest.raises(KeyError, match=r"Pos\(λy\. R\(alice, y\)\)|Pos\(λy\. R\(bob, y\)\)"):
        kleene_value(EVERY, {"Pos(λy. R(x, y))": 1.0}, domain=D)


def test_the_matrix_evaluator_reads_one_letter_for_each_individual():
    assert matrix_value(EVERY, INSTANCES, K3_MATRIX, domain=sorted(D)) == 0.0


def test_the_fuzzy_evaluator_reads_one_letter_for_each_individual():
    degrees = {"Pos(λy. R(alice, y))": 0.25, "Pos(λy. R(bob, y))": 0.75}
    assert fuzzy_evaluate(EVERY, degrees, domain=D) == 0.25
    assert (ground_quantifiers(EVERY, domain=D).to_unicode_str()
            == "Pos(λy. R(alice, y)) ∧ Pos(λy. R(bob, y))")


def test_some_is_not_every_over_two_individuals():
    """Not valid in LP (a matrix in which ``P → P`` is valid), by either decider, and not
    valid in Łukasiewicz logic."""
    assert manyvalued.is_valid(TO.parse("Pos(G) → Pos(G)"), "LP")
    assert not manyvalued.is_valid(WITNESS, "LP", domain=D)
    assert not matrix_is_valid(WITNESS, LP_MATRIX, domain=sorted(D))
    fuzzy = LukImplication(WITNESS.left, WITNESS.right)
    assert not fuzzy_is_valid(fuzzy, domain=D)
    # over one individual some is every
    assert manyvalued.is_valid(WITNESS, "LP", domain={"alice"})
    assert fuzzy_is_valid(fuzzy, domain={"alice"})


def test_a_variable_bound_by_the_lambda_term_itself_is_left_alone():
    """``∀y Pos(λy. R(y, y))``: the ``y`` of the body is the lambda's own."""
    node = TO.parse("∀y Pos(λy. R(y, y))")
    assert kleene_value(node, {"Pos(λy. R(y, y))": 1.0}, domain=D) == 1.0
    assert fuzzy_evaluate(node, {"Pos(λy. R(y, y))": 0.5}, domain=D) == 0.5


def test_an_atom_without_a_lambda_term_is_grounded_as_before():
    node = TO.parse("∀x Ess(G, x)")
    assert kleene_value(node, {"Ess(G, alice)": 1.0, "Ess(G, bob)": 0.5}, domain=D) == 0.5
    assert fuzzy_evaluate(node, {"Ess(G, alice)": 1.0, "Ess(G, bob)": 0.5}, domain=D) == 0.5
