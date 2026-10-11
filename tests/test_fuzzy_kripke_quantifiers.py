"""Quantifiers in the graded Kripke evaluator.

An individual quantifier is the infimum or supremum over the constant names of the
model's domain, the same at every world. A predicate quantifier is the infimum or
supremum over every fuzzy INTENSION of its predicate: a degree at each world for each
ground atom. Every expected degree is derived by hand from::

    □φ at w  =  inf over v of  R(w, v) → φ(v)        ◇φ at w  =  sup over v of  R(w, v) ⊗ φ(v)

with the truth functions of the t-norm (Łukasiewicz: ``x → y = min(1, 1 − x + y)``,
``x ⊗ y = max(0, x + y − 1)``; Gödel: ``x → y = 1 if x ≤ y else y``, ``x ⊗ y = min``).
"""

import itertools
import random
from fractions import Fraction

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.z3_fuzzy_kripke import predicate_quantifier_degree
from unicode_logic_kit.fol.nodes import (
    Atom, Box, Diamond, Knows, Constant, LukEquivalence, LukImplication, LukNegation,
    Quantifier, SecondOrderQuantifier, SortedQuantifier, StrongConjunction, StrongDisjunction,
    Variable, WeakConjunction, WeakDisjunction,
)
from unicode_logic_kit.semantics.fuzzy_kripke import FuzzyKripkeModel, satisfies_fuzzy_modal
from unicode_logic_kit.semantics.tnorm import GODEL, LUKASIEWICZ, PRODUCT, TNorm

MODAL = MSFLParser(fuzzy=True, modal=True)
MODAL_SORTED = MSFLParser(fuzzy=True, modal=True, many_sorted=True)
SO = MSFLParser(fuzzy=True, second_order=True, modal=True)
TO = MSFLParser(fuzzy=True, third_order=True, modal=True)

D = {"alice", "bob"}


def two_worlds(tnorm=LUKASIEWICZ, **individuals):
    """World 0 sees world 1 with weight 1/2; P is 1/4 of alice and 3/4 of bob there."""
    return FuzzyKripkeModel(
        {0, 1}, {"alethic": {(0, 1): 0.5}},
        {1: {"P(alice)": 0.25, "P(bob)": 0.75}}, tnorm=tnorm, **individuals)


# ---------------------------------------------------------------------------
# Individual quantifiers
# ---------------------------------------------------------------------------

INDIVIDUALS = [
    # ∀x P(x) at world 1 is min(1/4, 3/4); □ of it at 0 is 1/2 → 1/4 = min(1, 1 − 1/2 + 1/4).
    ("□∀x P(x)", LUKASIEWICZ, 0, 0.75),
    # Gödel: 1/2 → 1/4 = 1/4.
    ("□∀x P(x)", GODEL, 0, 0.25),
    # the same degree with the quantifier outside: min over x of (1/2 → P(x)) = min(3/4, 1).
    ("∀x □P(x)", LUKASIEWICZ, 0, 0.75),
    ("∀x □P(x)", GODEL, 0, 0.25),
    # ∃x ◇P(x): max over x of 1/2 ⊗ P(x) = max(0, 1/4).
    ("∃x ◇P(x)", LUKASIEWICZ, 0, 0.25),
    # Gödel: max over x of min(1/2, P(x)) = 1/2.
    ("∃x ◇P(x)", GODEL, 0, 0.5),
    # ◇∃x P(x): 1/2 ⊗ 3/4.
    ("◇∃x P(x)", LUKASIEWICZ, 0, 0.25),
    # at world 1 nothing is seen: □ of anything is 1, ◇ of anything is 0.
    ("∀x □P(x)", LUKASIEWICZ, 1, 1.0),
    ("∃x ◇P(x)", LUKASIEWICZ, 1, 0.0),
    # no modal operator: the degrees of world 1 themselves.
    ("∀x P(x)", LUKASIEWICZ, 1, 0.25),
    ("∃x P(x)", LUKASIEWICZ, 1, 0.75),
    # ∀x ∃y (P(x) → P(y)): y may be x.
    ("∀x ∃y (P(x) → P(y))", LUKASIEWICZ, 1, 1.0),
    # ∃x ∀y (P(y) → P(x)): x = bob.
    ("∃x ∀y (P(y) → P(x))", LUKASIEWICZ, 1, 1.0),
    # ∀x ∀y (P(x) → P(y)): bob to alice, 1 − 3/4 + 1/4.
    ("∀x ∀y (P(x) → P(y))", LUKASIEWICZ, 1, 0.5),
]


@pytest.mark.parametrize("text, tnorm, world, expected", INDIVIDUALS)
def test_an_individual_quantifier_ranges_over_the_domain_of_the_model(text, tnorm, world, expected):
    assert satisfies_fuzzy_modal(MODAL.parse(text), two_worlds(tnorm, domain=D), world) == expected


def test_the_domain_is_the_same_at_every_world():
    """Constant domains: the Barcan formula and its converse have degree 1."""
    model = two_worlds(domain=D)
    for text in ("∀x □P(x) → □∀x P(x)", "□∀x P(x) → ∀x □P(x)"):
        assert satisfies_fuzzy_modal(MODAL.parse(text), model, 0) == 1.0


def test_a_sorted_quantifier_ranges_over_the_universe_of_its_sort():
    model = two_worlds(sort_universes={"Human": {"alice"}, "Being": D})
    assert satisfies_fuzzy_modal(MODAL_SORTED.parse("□∀x:Human P(x)"), model, 0) == 0.75
    assert satisfies_fuzzy_modal(MODAL_SORTED.parse("□∃x:Being P(x)"), model, 0) == 1.0
    # a sorted constant is the constant
    assert satisfies_fuzzy_modal(MODAL_SORTED.parse("□P(alice:Human)"), model, 0) == 0.75


def test_an_agent_bound_by_a_quantifier_is_each_individual_in_turn():
    """``∀a K_a P``: the minimum over the agents of their own ``K``."""
    model = FuzzyKripkeModel(
        {0, 1}, {"K:alice": {(0, 1): 1.0}, "K:bob": {(0, 1): 0.5}},
        {1: {"P": 0.25}}, domain=D)
    # K_alice P = 1 → 1/4 = 1/4; K_bob P = 1/2 → 1/4 = 3/4
    assert satisfies_fuzzy_modal(MODAL.parse("∀a K_a P"), model, 0) == 0.25
    assert satisfies_fuzzy_modal(MODAL.parse("∃a K_a P"), model, 0) == 0.75


def test_a_quantifier_needs_its_universe():
    with pytest.raises(ValueError, match="∀x ranges over the domain, and no domain"):
        satisfies_fuzzy_modal(MODAL.parse("∀x P(x)"), two_worlds(), 0)
    with pytest.raises(ValueError, match="domain is empty"):
        satisfies_fuzzy_modal(MODAL.parse("∃x P(x)"), two_worlds(domain=()), 0)
    with pytest.raises(ValueError, match=r"no sort_universes\['Human'\]"):
        satisfies_fuzzy_modal(MODAL_SORTED.parse("∀x:Human P(x)"), two_worlds(domain=D), 0)
    hand_built = Quantifier("forall", Variable("x"), Atom("P", [Variable("x")]))
    with pytest.raises(ValueError, match="∀x ranges over the domain"):
        satisfies_fuzzy_modal(hand_built, two_worlds(), 0)
    assert satisfies_fuzzy_modal(hand_built, two_worlds(domain=D), 1) == 0.25
    sorted_one = SortedQuantifier("exists", Variable("x"), "S", Atom("P", [Variable("x")]))
    assert satisfies_fuzzy_modal(sorted_one, two_worlds(sort_universes={"S": D}), 1) == 0.75


def test_a_sorted_constant_outside_its_universe_is_refused():
    model = two_worlds(sort_universes={"Human": {"bob"}})
    with pytest.raises(ValueError, match="alice:Human names an element"):
        satisfies_fuzzy_modal(MODAL_SORTED.parse("□P(alice:Human)"), model, 0)


def test_a_model_shows_and_keeps_its_individuals():
    names = ["alice", "bob"]
    model = FuzzyKripkeModel({0}, domain=names, sort_universes={"S": names})
    names.append("carol")
    assert model.domain == frozenset(D) and model.sort_universes["S"] == frozenset(D)
    assert "domain=" in repr(model) and "sort_universes=" in repr(model)
    assert "domain=" not in repr(FuzzyKripkeModel({0}))


# ---------------------------------------------------------------------------
# Predicate quantifiers
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("tnorm, loop", itertools.product([LUKASIEWICZ, GODEL], [0.0, 0.25, 0.75, 1.0]))
def test_reflexivity_has_the_degree_of_the_loop(tnorm, loop):
    """``∀P (□P → P)`` at ``w`` has the degree ``R(w, w)``.

    Let ``r = R(w, w)`` and ``p`` the degree of ``P`` at ``w``; at every other world ``P``
    may be 1, which leaves ``□P = r → p``. Łukasiewicz: for ``p ≤ r`` the body is
    ``1 − (1 − r + p) + p = r``, and for ``p > r`` it is ``p > r``. Gödel: for ``p < r`` it
    is ``p → p = 1``, and for ``p ≥ r`` it is ``1 → p = p ≥ r``. The infimum is ``r``.
    """
    model = FuzzyKripkeModel({0, 1}, {"alethic": {(0, 0): loop, (0, 1): 0.5}}, tnorm=tnorm)
    assert satisfies_fuzzy_modal(SO.parse("∀P (□P → P)"), model, 0) == loop
    # world 1 sees nothing: □P = 1 there for every P, and P may be 0
    assert satisfies_fuzzy_modal(SO.parse("∀P (□P → P)"), model, 1) == 0.0


@pytest.mark.parametrize("tnorm, expected", [(LUKASIEWICZ, 0.75), (GODEL, 0.25)])
def test_transitivity_has_the_degree_of_the_missing_shortcut(tnorm, expected):
    """``∀P (□P → □□P)`` at 0, with ``0 → 1 → 2`` at 3/4 each and the shortcut ``0 → 2`` at 1/4.

    ``□□P`` at 0 is ``(3/4 ⊗ 3/4) → P(2)`` and, with ``P(1) = 1``, ``□P`` is ``1/4 → P(2)``.
    The infimum over ``P(2)`` of the implication between them is ``(3/4 ⊗ 3/4) → 1/4``:
    Łukasiewicz ``1/2 → 1/4 = 3/4``, Gödel ``3/4 → 1/4 = 1/4``.
    """
    model = FuzzyKripkeModel(
        {0, 1, 2}, {"alethic": {(0, 1): 0.75, (1, 2): 0.75, (0, 2): 0.25}}, tnorm=tnorm)
    assert satisfies_fuzzy_modal(SO.parse("∀P (□P → □□P)"), model, 0) == expected


def test_a_bound_predicate_is_an_intension():
    """``∃P (P ⊗ □¬P)``: ``P`` is 1 here and 0 at the world seen, so the degree is 1.
    A predicate with one degree for all worlds could reach ``p ⊗ (1/2 → 1 − p)`` only,
    which is at most 1/2."""
    model = FuzzyKripkeModel({0, 1}, {"alethic": {(0, 1): 0.5}})
    assert satisfies_fuzzy_modal(SO.parse("∃P (P ⊗ □¬P)"), model, 0) == 1.0


def test_a_predicate_quantifier_over_individuals_at_worlds():
    model = two_worlds(domain=D)
    # ∃R □∀x (R(x) ↔ P(x)): R may be P at world 1
    assert satisfies_fuzzy_modal(SO.parse("∃R □∀x (R(x) ↔ P(x))"), model, 0) == 1.0
    # ∀R □∀x (R(x) → P(x)): R = 1 at world 1: 1/2 → min(1/4, 3/4)
    assert satisfies_fuzzy_modal(SO.parse("∀R □∀x (R(x) → P(x))"), model, 0) == 0.75
    # ∀R (□R(alice) → □P(alice)) at 0: R(alice) = 1 at 1: 1 → (1/2 → 1/4) = 3/4
    assert satisfies_fuzzy_modal(SO.parse("∀R (□R(alice) → □P(alice))"), model, 0) == 0.75


def test_a_quantifier_whose_body_does_not_read_the_predicate():
    model = two_worlds(domain=D)
    assert satisfies_fuzzy_modal(SO.parse("∀R □P(alice)"), model, 0) == 0.75
    # at world 1 nothing is seen, so □R reads R at no world
    assert satisfies_fuzzy_modal(SO.parse("∀R □R"), model, 1) == 1.0


def test_a_predicate_quantifier_needs_a_linear_tnorm():
    scaled = TNorm("lukasiewicz", LUKASIEWICZ.conj, LUKASIEWICZ.disj,
                   LUKASIEWICZ.impl, LUKASIEWICZ.neg)
    for tnorm in (PRODUCT, scaled):
        model = FuzzyKripkeModel({0}, {"alethic": {(0, 0): 0.5}}, tnorm=tnorm)
        with pytest.raises(NotImplementedError, match="not tnorm.LUKASIEWICZ or tnorm.GODEL"):
            satisfies_fuzzy_modal(SO.parse("∀P (□P → P)"), model, 0)
    # without a predicate quantifier the product t-norm evaluates as before
    model = FuzzyKripkeModel({0}, {"alethic": {(0, 0): 0.5}}, {0: {"P": 0.25}}, tnorm=PRODUCT)
    assert satisfies_fuzzy_modal(SO.parse("◇P"), model, 0) == 0.125


def test_a_bound_predicate_in_argument_position_is_refused():
    model = two_worlds(domain=D)
    with pytest.raises(NotImplementedError, match="G is bound .* argument position"):
        satisfies_fuzzy_modal(TO.parse("∀G (Pos(G) → □Pos(G))"), model, 0)


def test_a_bound_predicate_has_one_arity():
    node = SecondOrderQuantifier("∀", "P", 1, Box(Atom("P", [])))
    with pytest.raises(ValueError, match="binds P at arity 1"):
        satisfies_fuzzy_modal(node, FuzzyKripkeModel({0}, {"alethic": {(0, 0): 1.0}}), 0)


# ---------------------------------------------------------------------------
# Third-order atoms
# ---------------------------------------------------------------------------

def test_a_third_order_atom_is_a_letter_of_the_world():
    model = FuzzyKripkeModel(
        {0, 1}, {"alethic": {(0, 1): 0.5}},
        {0: {"Pos(G)": 1.0}, 1: {"Pos(G)": 0.25, "Pos(λx. ¬G(x))": 0.75}})
    assert satisfies_fuzzy_modal(TO.parse("Pos(G)"), model, 0) == 1.0
    # 1 → (1/2 → 1/4)
    assert satisfies_fuzzy_modal(TO.parse("Pos(G) → □Pos(G)"), model, 0) == 0.75
    # 1/2 ⊗ 3/4
    assert satisfies_fuzzy_modal(TO.parse("◇Pos(λx. ¬G(x))"), model, 0) == 0.25
    # the property is taken by name: Pos(H) is another letter, absent and so 0
    assert satisfies_fuzzy_modal(TO.parse("Pos(H)"), model, 0) == 0.0


def test_an_individual_inside_a_property_argument_is_grounded():
    model = FuzzyKripkeModel(
        {0}, valuation={0: {"Ess(λy. R(alice, y), alice)": 0.25,
                            "Ess(λy. R(bob, y), bob)": 0.75}}, domain=D)
    node = TO.parse("∀x Ess(λy. R(x, y), x)")
    assert satisfies_fuzzy_modal(node, model, 0) == 0.25


# ---------------------------------------------------------------------------
# The exact route against the evaluator
# ---------------------------------------------------------------------------

def random_formula(rng, depth):
    if depth == 0 or rng.random() < 0.2:
        return Atom(rng.choice("PQ"), [])
    kind = rng.randrange(10)
    sub = lambda: random_formula(rng, depth - 1)        # noqa: E731
    if kind == 0:
        return LukNegation(sub())
    if kind == 1:
        return Box(sub())
    if kind == 2:
        return Diamond(sub())
    if kind == 3:
        return Knows(Constant("alice"), sub())
    binary = (WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
              LukImplication, LukEquivalence)
    return binary[kind - 4](sub(), sub())


def random_model(rng, tnorm):
    eighths = [k / 8 for k in range(9)]
    worlds = range(3)
    return FuzzyKripkeModel(
        worlds,
        {name: {(w, v): rng.choice(eighths) for w in worlds for v in worlds}
         for name in ("alethic", "K:alice")},
        {w: {"P": rng.choice(eighths), "Q": rng.choice(eighths)} for w in worlds},
        tnorm=tnorm)


@pytest.mark.parametrize("tnorm", [LUKASIEWICZ, GODEL])
def test_the_exact_degree_is_the_degree_the_evaluator_computes(tnorm):
    """Two computations of one definition: the floats of the evaluator and the rationals of
    the arithmetic encoding. On weights and degrees in eighths the floats are exact too."""
    rng = random.Random(20261011)
    for _ in range(120):
        formula = random_formula(rng, 3)
        model = random_model(rng, tnorm)
        world = rng.randrange(3)
        exact = predicate_quantifier_degree(formula, model, world)
        assert isinstance(exact, Fraction)
        assert float(exact) == satisfies_fuzzy_modal(formula, model, world), formula.to_unicode_str()


@pytest.mark.parametrize("tnorm", [LUKASIEWICZ, GODEL])
def test_the_infimum_is_below_the_body_at_every_interpretation_tried(tnorm):
    """``∀P φ ≤ φ`` with ``P`` read from the valuation, whatever degrees it has there."""
    rng = random.Random(7)
    for _ in range(25):
        body = random_formula(rng, 2)
        model = random_model(rng, tnorm)
        lower = satisfies_fuzzy_modal(SecondOrderQuantifier("∀", "P", 0, body), model, 0)
        upper = satisfies_fuzzy_modal(SecondOrderQuantifier("∃", "P", 0, body), model, 0)
        here = satisfies_fuzzy_modal(body, model, 0)
        assert lower <= here <= upper, body.to_unicode_str()


# ---------------------------------------------------------------------------
# When Z3 does not answer
# ---------------------------------------------------------------------------

def test_a_degree_z3_does_not_determine_is_an_error_and_not_a_number(monkeypatch):
    import z3

    from unicode_logic_kit.atp import z3_fuzzy_kripke

    class Undecided(z3.Solver):
        def check(self, *assumptions):
            return z3.unknown

    monkeypatch.setattr(z3_fuzzy_kripke, "Solver", Undecided)
    model = FuzzyKripkeModel({0}, {"alethic": {(0, 0): 0.5}})
    with pytest.raises(RuntimeError, match="did not determine the degree of a predicate quantifier"):
        satisfies_fuzzy_modal(SO.parse("∀P (□P → P)"), model, 0)


# ---------------------------------------------------------------------------
# Correspondence, with a degree
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("tnorm", [LUKASIEWICZ, GODEL])
def test_the_degree_of_reflexivity_and_of_transitivity_in_random_models(tnorm):
    """Two facts that hold under every t-norm with a residuum, checked against the optimum.

    ``∀P (□P → P)`` at ``w`` is ``R(w, w)``: ``□P ≤ R(w, w) → P(w)`` gives ``R(w, w) ≤ □P →
    P(w)``, and ``P = R(w, ·)`` has ``□P = 1`` and ``P(w) = R(w, w)``.

    ``∀P (□P → □□P)`` at ``w`` is the infimum over ``v`` and ``u`` of ``(R(w, v) ⊗ R(v, u)) →
    R(w, u)``: with ``S(u)`` the supremum over ``v`` of ``R(w, v) ⊗ R(v, u)``, ``□□P`` is the
    infimum of ``S(u) → P(u)``; ``(R(w, u) → P(u)) ⊗ (S(u) → R(w, u)) ≤ S(u) → P(u)`` gives
    the lower bound, and ``P = R(w, ·)`` reaches it.
    """
    rng = random.Random(4)
    eighths = [k / 8 for k in range(9)]
    worlds = range(3)
    for _ in range(12):
        weight = {(w, v): rng.choice(eighths) for w in worlds for v in worlds}
        model = FuzzyKripkeModel(worlds, {"alethic": weight}, tnorm=tnorm)
        assert satisfies_fuzzy_modal(SO.parse("∀P (□P → P)"), model, 0) == weight[(0, 0)]
        shortcut = min(tnorm.impl(tnorm.conj(weight[(0, v)], weight[(v, u)]), weight[(0, u)])
                       for v in worlds for u in worlds)
        assert satisfies_fuzzy_modal(SO.parse("∀P (□P → □□P)"), model, 0) == shortcut
