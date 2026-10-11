"""A predicate quantifier of a fuzzy formula ranges over the fuzzy interpretations.

``∀P φ`` is the infimum of ``φ`` over every assignment of a degree in [0, 1] to each
ground atom of ``P`` that ``φ`` reads, and ``∃P φ`` the supremum. Every expected degree
below is derived by hand, in the comment next to it, from the truth functions::

    Łukasiewicz   ¬x = 1 − x              x ⊗ y = max(0, x + y − 1)
                  x ⊕ y = min(1, x + y)   x → y = min(1, 1 − x + y)
    Gödel         ¬x = 1 if x = 0 else 0  x ⊗ y = min(x, y)
                  x ⊕ y = max(x, y)       x → y = 1 if x ≤ y else y
    both          x ∧ y = min(x, y)       x ∨ y = max(x, y)       x ↔ y = min(x → y, y → x)

The degrees are exact: an optimum over a real cube, computed as linear real
arithmetic, also where it is approached and not reached.
"""

import itertools

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.z3_fuzzy import (
    degree_expr, fuzzy_get_model, fuzzy_is_satisfiable, fuzzy_is_valid,
)
from unicode_logic_kit.fol.nodes import Atom, SecondOrderQuantifier, WeakDisjunction, LukNegation
from unicode_logic_kit.semantics.fuzzy import evaluate

SO = MSFLParser(fuzzy=True, second_order=True)
SO_SORTED = MSFLParser(fuzzy=True, second_order=True, many_sorted=True)
TO = MSFLParser(fuzzy=True, third_order=True)
MODAL_SO = MSFLParser(fuzzy=True, second_order=True, modal=True)

L, G = "lukasiewicz", "godel"
D = {"alice", "bob"}
Q = {"Q": 0.25, "Q(alice)": 0.25, "Q(bob)": 0.75}


# ---------------------------------------------------------------------------
# The degree under one valuation
# ---------------------------------------------------------------------------

PROPOSITIONAL = [
    # max(p, 1 − p): the two lines cross at p = 1/2.
    ("∀P (P ∨ ¬P)", L, 0.5),
    # ¬p is 1 at p = 0 and 0 above it, so max(p, ¬p) is 1 at 0 and p above: the infimum 0
    # is approached and never reached.
    ("∀P (P ∨ ¬P)", G, 0.0),
    # min(p, 1 − p) is largest at p = 1/2.
    ("∃P (P ∧ ¬P)", L, 0.5),
    # min(p, ¬p) = 0 for every p.
    ("∃P (P ∧ ¬P)", G, 0.0),
    # min(1, p + (1 − p)) = 1 for every p.
    ("∀P (P ⊕ ¬P)", L, 1.0),
    # ⊕ is max under Gödel: the case of ∨ above.
    ("∀P (P ⊕ ¬P)", G, 0.0),
    # max(0, p + (1 − p) − 1) = 0 for every p.
    ("∃P (P ⊗ ¬P)", L, 0.0),
    # x ⊗ x ≤ x under every t-norm.
    ("∀P (P ⊗ P → P)", L, 1.0),
    ("∀P (P ⊗ P → P)", G, 1.0),
    # p ≤ 1/2: p ⊗ p = 0, so the degree is 1 − p ≥ 1/2. p ≥ 1/2: 1 − p + (2p − 1) = p ≥ 1/2.
    ("∀P (P → P ⊗ P)", L, 0.5),
    # min(p, p) = p.
    ("∀P (P → P ⊗ P)", G, 1.0),
    # 1 − (1 − p) = p.
    ("∀P (¬¬P → P)", L, 1.0),
    # ¬¬p = 1 for every p > 0, and 1 → p = p: the infimum over p > 0 is 0.
    ("∀P (¬¬P → P)", G, 0.0),
    # p → 1/4 is smallest at p = 1: 1/4.
    ("∀P (P → Q)", L, 0.25),
    # 1 for p ≤ 1/4 and 1/4 above.
    ("∀P (P → Q)", G, 0.25),
    # p = 0 gives 1.
    ("∃P (P → Q)", L, 1.0),
    # P may be Q.
    ("∃P (P ↔ Q)", L, 1.0),
    ("∃P (P ↔ Q)", G, 1.0),
    # for a fixed r the infimum over p of 1 − |r − p| is min(r, 1 − r); largest at r = 1/2.
    ("∃R ∀P (R ↔ P)", L, 0.5),
    # r ↔ p = min(r, p) for r ≠ p, and some p makes that 0.
    ("∃R ∀P (R ↔ P)", G, 0.0),
    # R may be ¬P.
    ("∀P ∃R (R ↔ ¬P)", L, 1.0),
    ("∀P ∃R (R ↔ ¬P)", G, 1.0),
    # r ⊗ r = max(0, 2r − 1) = p at r = (1 + p) / 2.
    ("∀P ∃R ((R ⊗ R) ↔ P)", L, 1.0),
    # for a fixed r the infimum over p of p → r is r (at p = 1); largest at r = 1.
    ("∃R ∀P (P → R)", L, 1.0),
    # the supremum over r of p ⊗ r is p (at r = 1), and the infimum of that over p is 0.
    ("∀P ∃R (P ⊗ R)", L, 0.0),
    # ∀P P is the bottom degree, ∃P P the top one.
    ("∀P P", L, 0.0),
    ("∃P P", G, 1.0),
    # an inner quantifier of the same name is another predicate: ∃P ¬P = 1, so the body is 1.
    ("∀P (P ∨ ∃P ¬P)", L, 1.0),
    # ∀P P = 0 inside, so the body is p → 0 = 1 − p, smallest at p = 1.
    ("∀P (P → ∀P P)", L, 0.0),
]


@pytest.mark.parametrize("text, tnorm, expected", PROPOSITIONAL)
def test_the_degree_of_a_predicate_quantifier(text, tnorm, expected):
    assert evaluate(SO.parse(text), Q, tnorm=tnorm) == expected


OVER_INDIVIDUALS = [
    # comprehension: P may be Q itself.
    ("∃P ∀x (P(x) ↔ Q(x))", L, 1.0),
    ("∃P ∀x (P(x) ↔ Q(x))", G, 1.0),
    # min over x of (p_x → Q(x)), smallest at p = 1 everywhere: min(1/4, 3/4).
    ("∀P ∀x (P(x) → Q(x))", L, 0.25),
    ("∀P ∀x (P(x) → Q(x))", G, 0.25),
    # the same with the quantifiers exchanged: the minimum over x of Q(x).
    ("∀x ∀P (P(x) → Q(x))", L, 0.25),
    # p = 1 at the x where ¬Q(x) is largest: 1 − 1/4.
    ("∃P ∃x (P(x) ⊗ ¬Q(x))", L, 0.75),
    # ¬Q(x) = 0 for both, Q being above 0.
    ("∃P ∃x (P(x) ⊗ ¬Q(x))", G, 0.0),
    # P true of alice to degree 1 and of bob to degree 0.
    ("∀P (P(alice) → P(bob))", L, 0.0),
    ("∀P (P(alice) → P(bob))", G, 0.0),
    ("∃P (P(alice) ⊗ ¬P(bob))", L, 1.0),
    ("∃P (P(alice) ⊗ ¬P(bob))", G, 1.0),
    ("∀P (P(alice) → P(alice))", L, 1.0),
    # the minimum of two degrees is at most their maximum.
    ("∀P (∀x P(x) → ∃x P(x))", L, 1.0),
    # 1 → 0 at P(alice) = 1, P(bob) = 0.
    ("∀P (∃x P(x) → ∀x P(x))", L, 0.0),
    # a binary predicate: R(x, y) may be min(Q(x), Q(y)) at each of the four pairs.
    ("∃R ∀x ∀y (R(x, y) ↔ (Q(x) ∧ Q(y)))", L, 1.0),
    # for a fixed interpretation of P the inner supremum is 1 (R = P), at every x.
    ("∀P ∃R ∀x (R(x) ↔ P(x))", L, 1.0),
]


@pytest.mark.parametrize("text, tnorm, expected", OVER_INDIVIDUALS)
def test_the_degree_over_a_domain_of_two(text, tnorm, expected):
    assert evaluate(SO.parse(text), Q, domain=D, tnorm=tnorm) == expected


def test_a_bound_atom_is_not_looked_up_in_the_valuation():
    assert evaluate(SO.parse("∀P (P ∨ ¬P)"), {"P": 1.0}) == 0.5


@pytest.mark.parametrize("free, expected", [(0.25, 0.25), (0.75, 0.5)])
def test_an_occurrence_outside_the_quantifier_is_free(free, expected):
    """``P ∧ ∀P (P ∨ ¬P)``: the first ``P`` is the valuation's, min(P, 1/2)."""
    assert evaluate(SO.parse("P ∧ ∀P (P ∨ ¬P)"), {"P": free}) == expected


def test_a_quantifier_under_connectives():
    # Q ⊕ ∀P (P(bob) → Q(bob)) = min(1, 1/4 + 3/4)
    assert evaluate(SO.parse("Q(alice) ⊕ ∀P (P(bob) → Q(bob))"), Q) == 1.0
    # ¬∀P (P ∨ ¬P) = 1 − 1/2
    assert evaluate(SO.parse("¬∀P (P ∨ ¬P)"), {}) == 0.5
    # (∀P (P ∨ ¬P)) ⊗ (∃P (P ∧ ¬P)) = max(0, 1/2 + 1/2 − 1)
    assert evaluate(SO.parse("(∀P (P ∨ ¬P)) ⊗ (∃P (P ∧ ¬P))"), {}) == 0.0


def test_sorted_individuals_under_a_predicate_quantifier():
    universes = {"S": D}
    assert evaluate(SO_SORTED.parse("∃P ∀x:S (P(x) ↔ Q(x))"), Q, sort_universes=universes) == 1.0
    assert evaluate(SO_SORTED.parse("∀P ∀x:S (P(x) → Q(x))"), Q, sort_universes=universes) == 0.25
    # a sorted constant is the constant: P(alice:S) and P(alice) are one bound atom
    assert evaluate(SO_SORTED.parse("∀P (P(alice:S) → P(alice:S))"), {}) == 1.0


def test_the_interpretations_are_fuzzy_and_not_crisp():
    """Comprehension has degree 1 because ``P`` may take the degree 1/2 of ``Q``. Over
    crisp ``P`` it would be 1/2: the better of 1 − |0 − 1/2| and 1 − |1 − 1/2|."""
    half = {"Q(alice)": 0.5}
    assert evaluate(SO.parse("∃P ∀x (P(x) ↔ Q(x))"), half, domain={"alice"}) == 1.0
    crisp = max(evaluate(SO.parse("∀x (P(x) ↔ Q(x))"), {**half, "P(alice)": p},
                         domain={"alice"}) for p in (0.0, 1.0))
    assert crisp == 0.5


GRID = [k / 8 for k in range(9)]
BODIES = ["P ∨ ¬P", "P ∧ ¬P", "P → P ⊗ P", "(P → Q) ∧ (Q → P)", "(P ⊕ Q) ⊗ ¬P",
          "¬(P ↔ Q) ∨ (P ⊗ Q)", "(P → Q) → Q", "P ⊕ P ⊕ ¬Q"]


@pytest.mark.parametrize("body, tnorm, q", itertools.product(BODIES, [L, G], [0.0, 0.25, 0.5, 1.0]))
def test_the_optimum_bounds_every_value_of_the_body(body, tnorm, q):
    """The infimum is at most, and the supremum at least, the degree of the body at each
    degree of ``P`` on a grid, where ``P`` is an atom of the valuation."""
    free = SO.parse(body)
    values = [evaluate(free, {"P": p, "Q": q}, tnorm=tnorm) for p in GRID]
    assert evaluate(SO.parse(f"∀P ({body})"), {"Q": q}, tnorm=tnorm) <= min(values)
    assert evaluate(SO.parse(f"∃P ({body})"), {"Q": q}, tnorm=tnorm) >= max(values)


@pytest.mark.parametrize("body, q", itertools.product(BODIES, [0.0, 0.25, 0.5, 1.0]))
def test_the_lukasiewicz_optimum_is_reached_on_the_grid(body, q):
    """The Łukasiewicz connectives are continuous and piecewise linear with integer slopes,
    so for a ``Q`` in eighths the optimum of these bodies lies at a multiple of 1/8."""
    free = SO.parse(body)
    values = [evaluate(free, {"P": p, "Q": q}) for p in GRID]
    assert evaluate(SO.parse(f"∀P ({body})"), {"Q": q}) == min(values)
    assert evaluate(SO.parse(f"∃P ({body})"), {"Q": q}) == max(values)


# ---------------------------------------------------------------------------
# What is refused
# ---------------------------------------------------------------------------

def test_the_product_tnorm_is_refused_by_name():
    with pytest.raises(NotImplementedError, match="product t-norm is not linear"):
        evaluate(SO.parse("∀P (P ∨ ¬P)"), {}, tnorm="product")
    with pytest.raises(NotImplementedError, match="product"):
        fuzzy_is_valid(SO.parse("∀P (P ⊕ ¬P)"), tnorm="product")
    # without a predicate quantifier the evaluator has the product t-norm as before
    assert evaluate(SO.parse("P ⊗ P"), {"P": 0.5}, tnorm="product") == 0.25


def test_a_bound_predicate_in_argument_position_is_refused():
    text = "∀G (Pos(G) → ∃x G(x))"
    with pytest.raises(NotImplementedError, match="G is bound .* argument position"):
        evaluate(TO.parse(text), {"Pos(G)": 1.0}, domain=D)
    with pytest.raises(NotImplementedError, match="argument position"):
        evaluate(TO.parse(text), {}, domain=D, functionals={"Pos": lambda g: 1.0})
    with pytest.raises(NotImplementedError, match="argument position"):
        fuzzy_is_valid(TO.parse("∀G (Pos(G) → Pos(G))"))
    with pytest.raises(NotImplementedError, match="argument position"):
        evaluate(TO.parse("∀G Pos(λx. ¬G(x))"), {})


def test_a_free_third_order_atom_under_a_predicate_quantifier_is_a_letter():
    # inf over p of (p → 1/2) = 1/2
    assert evaluate(TO.parse("∀P (P(alice) → Pos(G))"), {"Pos(G)": 0.5}) == 0.5


def test_a_bound_predicate_has_one_arity():
    node = SecondOrderQuantifier("∀", "P", 1, WeakDisjunction(Atom("P", []), LukNegation(Atom("P", []))))
    with pytest.raises(ValueError, match="binds P at arity 1"):
        evaluate(node, {})


def test_a_modal_operator_has_no_degree_under_one_valuation():
    node = MODAL_SO.parse("∀P (□P → P)")
    with pytest.raises(TypeError, match="satisfies_fuzzy_modal"):
        evaluate(node, {})
    with pytest.raises(TypeError, match="fuzzy_modal_search"):
        fuzzy_is_valid(node)
    with pytest.raises(TypeError, match="fuzzy_modal_search"):
        fuzzy_is_valid(MODAL_SO.parse("□P → □P"))


def test_a_missing_universe_and_a_missing_atom_are_named():
    with pytest.raises(ValueError, match="no domain"):
        evaluate(SO.parse("∀P ∀x P(x)"), {})
    with pytest.raises(KeyError, match="No degree for ground atom 'Q'"):
        evaluate(SO.parse("∀P (P → Q)"), {})


# ---------------------------------------------------------------------------
# Validity and satisfiability
# ---------------------------------------------------------------------------

VALID = [
    ("∀P (P ⊕ ¬P)", L, True),
    ("∀P (P ∨ ¬P)", L, False),
    ("∀P (P ⊗ P → P)", L, True),
    ("∀P (P → P ⊗ P)", L, False),
    ("∀P (P → P ⊗ P)", G, True),
    ("∀P (¬¬P → P)", L, True),
    ("∀P (¬¬P → P)", G, False),
    # hypothetical syllogism, for every degree of the bound P and of the free Q, R
    ("∀P ((P → Q) → ((Q → R) → (P → R)))", L, True),
    ("∀P ((P → Q) → ((Q → R) → (P → R)))", G, True),
    # P may be Q, ¬Q, or the square root of Q
    ("∃P (P ↔ Q)", L, True),
    ("∃P (P ↔ ¬Q)", G, True),
    ("∃P ((P ⊗ P) ↔ Q)", L, True),
    # P ⊗ ¬P is 0 for every P
    ("∃P (P ⊗ ¬P)", L, False),
    # ∀P P is the bottom degree and ∃P P the top one
    ("(∀P P) → Q", L, True),
    ("Q → ∃P P", G, True),
    ("Q → ∀P P", L, False),
    # instantiation and generalisation
    ("(∀P (P ∨ ¬P)) → (Q ∨ ¬Q)", L, True),
    ("(Q ∧ ¬Q) → ∃P (P ∧ ¬P)", L, True),
    ("(Q ∨ ¬Q) → ∀P (P ∨ ¬P)", L, False),
    # the degree 1/2 of ∀P (P ∨ ¬P), stated in the object language
    ("(∀P (P ∨ ¬P)) ⊕ (∀P (P ∨ ¬P))", L, True),
    ("(∀P (P ∨ ¬P)) ⊗ (∀P (P ∨ ¬P))", L, False),
]


@pytest.mark.parametrize("text, tnorm, expected", VALID)
def test_validity_with_predicate_quantifiers(text, tnorm, expected):
    assert fuzzy_is_valid(SO.parse(text), tnorm=tnorm) is expected


@pytest.mark.parametrize("tnorm", [L, G])
def test_comprehension_is_valid_over_a_domain(tnorm):
    assert fuzzy_is_valid(SO.parse("∃P ∀x (P(x) ↔ Q(x))"), domain=D, tnorm=tnorm)
    assert fuzzy_is_valid(SO.parse("∀P ∃R ∀x (R(x) ↔ ¬P(x))"), domain=D, tnorm=tnorm)
    assert not fuzzy_is_valid(SO.parse("∀P ∀x (P(x) → Q(x))"), domain=D, tnorm=tnorm)


def test_satisfiability_reads_the_optimum_exactly():
    # the supremum 1/2 of P ∧ ¬P is reached and not exceeded
    node = SO.parse("∃P (P ∧ ¬P)")
    assert fuzzy_is_satisfiable(node, threshold=0.5)
    assert not fuzzy_is_satisfiable(node, threshold=0.5, strict=True)
    # Q ∧ ¬∀P (P → Q) = min(q, 1 − q)
    node = SO.parse("Q ∧ ¬∀P (P → Q)")
    assert fuzzy_is_satisfiable(node, threshold=0.5)
    assert not fuzzy_is_satisfiable(node, threshold=0.625)


def test_a_model_holds_the_free_atoms_only():
    # Q ⊗ ∀P (P → Q) = q ⊗ q, which is 1 at q = 1 only
    model = fuzzy_get_model(SO.parse("Q ⊗ ∀P (P → Q)"))
    assert model == {"Q": 1.0, "degree": 1.0}
    assert fuzzy_get_model(SO.parse("∃P (P ⊗ ¬P)")) is None


def test_the_degree_expression_has_no_unknown_for_a_bound_atom():
    _, _, atom_vars = degree_expr(SO.parse("Q ⊗ ∀P (P(alice) → Q)"))
    assert set(atom_vars) == {"Q"}


# ---------------------------------------------------------------------------
# Two terms and one individual
# ---------------------------------------------------------------------------

def test_a_decider_refuses_bound_predicates_over_terms_that_may_be_one_individual():
    """``∃P (P(alice) ⊗ ¬P(bob))`` says that alice and bob differ. Read with each term as
    its own individual it has degree 1 under every valuation; in a model where the two
    names denote one individual it has degree 0."""
    node = SO.parse("∃P (P(alice) ⊗ ¬P(bob))")
    with pytest.raises(NotImplementedError, match="different terms alice and bob"):
        fuzzy_is_valid(node)
    with pytest.raises(NotImplementedError, match="may name one individual"):
        fuzzy_is_satisfiable(node)
    with pytest.raises(NotImplementedError, match="not a name of the declared domain"):
        fuzzy_is_valid(node, domain={"alice"})


def test_two_names_of_the_declared_domain_are_two_individuals():
    assert fuzzy_is_valid(SO.parse("∃P (P(alice) ⊗ ¬P(bob))"), domain=D)
    assert fuzzy_is_valid(SO_SORTED.parse("∃P (P(alice:S) ⊗ ¬P(bob:S))"),
                          sort_universes={"S": D})


def test_one_term_under_bound_predicates_needs_no_declaration():
    assert fuzzy_is_valid(SO.parse("∀P (P(alice) → P(alice))"))
    assert fuzzy_is_valid(SO.parse("∀P ∃R (R(alice) ↔ ¬P(alice))"))


def test_a_function_term_is_no_name_of_the_domain():
    with pytest.raises(NotImplementedError, match=r"f\(alice\)"):
        fuzzy_is_valid(SO.parse("∃P (P(f(alice)) ⊗ ¬P(alice))"), domain={"alice"})


def test_the_evaluation_of_one_valuation_reads_a_term_as_its_own_individual():
    """A valuation is one model, and in it two terms are two individuals."""
    assert evaluate(SO.parse("∃P (P(alice) ⊗ ¬P(bob))"), {}) == 1.0


def test_a_free_variable_next_to_a_quantifier_is_refused_as_before():
    with pytest.raises(NotImplementedError, match="free in a quantified formula"):
        fuzzy_is_valid(SO.parse("∀P ∀y (P(y) → P(x))"), domain=D)


# ---------------------------------------------------------------------------
# Grounding
# ---------------------------------------------------------------------------

def test_an_individual_quantifier_is_grounded_under_a_predicate_quantifier_and_a_box():
    from unicode_logic_kit.semantics.fuzzy import ground_quantifiers

    grounded = ground_quantifiers(SO.parse("∃P ∀x (P(x) ↔ Q(x))"), domain=D)
    assert grounded.to_unicode_str() == "∃P ((P(alice) ↔ Q(alice)) ∧ (P(bob) ↔ Q(bob)))"
    grounded = ground_quantifiers(MODAL_SO.parse("□∀x K_x P(x)"), domain=D)
    assert grounded.to_unicode_str() == "□(K_alice P(alice) ∧ K_bob P(bob))"
