"""The bounded search for a countermodel of a fuzzy modal formula.

A countermodel gives the formula a degree below 1 at world 0. What the search reports
for each formula below is known by hand: either a countermodel is written down in the
comment, or the formula has degree 1 in every model of the class, by the argument given.
With ``R`` the weight of an edge, ``→`` the residuum and ``⊗`` the t-norm::

    □φ at w  =  inf over v of  R(w, v) → φ(v)        ◇φ at w  =  sup over v of  R(w, v) ⊗ φ(v)
"""

import json
import random

import pytest
import z3

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp import z3_fuzzy_kripke
from unicode_logic_kit.atp.z3_fuzzy_kripke import (
    FuzzyModalSearchResult, fuzzy_kripke_model_from_dict, fuzzy_kripke_model_to_dict,
    fuzzy_modal_countermodel, fuzzy_modal_search,
)
from unicode_logic_kit.semantics.fuzzy_kripke import FuzzyKripkeModel, satisfies_fuzzy_modal
from unicode_logic_kit.semantics.tnorm import GODEL, LUKASIEWICZ

MODAL = MSFLParser(fuzzy=True, modal=True)
SO = MSFLParser(fuzzy=True, second_order=True, modal=True)
TO = MSFLParser(fuzzy=True, third_order=True, modal=True)
SORTED = MSFLParser(fuzzy=True, modal=True, many_sorted=True)

L, G = "lukasiewicz", "godel"
D = {"alice", "bob"}


def search(text, parser=MODAL, **options):
    return fuzzy_modal_search(parser.parse(text), **options)


def assert_countermodel(result, text, parser=MODAL, worlds=None):
    assert result.model is not None and not result.exhausted and not result.timed_out
    assert result.unsupported is None
    degree = satisfies_fuzzy_modal(parser.parse(text), result.model, 0)
    assert degree == result.degree < 1.0
    if worlds is not None:
        assert result.worlds == worlds == len(result.model.worlds)


def assert_none_up_to(result, bound=3):
    assert result.model is None and result.degree is None
    assert result.exhausted and not result.timed_out and result.unsupported is None
    assert result.worlds == bound
    assert "not a proof of validity" in result.detail


# ---------------------------------------------------------------------------
# The axiom K and the weight of an edge
# ---------------------------------------------------------------------------

K_AXIOM = "□(P → Q) → (□P → □Q)"


def test_the_axiom_k_fails_over_a_fuzzy_frame_under_lukasiewicz():
    """One world that sees itself with weight 1/2, ``P = 1/2``, ``Q = 0``: ``□(P → Q) =
    1/2 → 1/2 = 1``, ``□P = 1/2 → 1/2 = 1``, ``□Q = 1/2 → 0 = 1/2``; the axiom has degree
    ``1 → (1 → 1/2) = 1/2``."""
    by_hand = FuzzyKripkeModel({0}, {"alethic": {(0, 0): 0.5}}, {0: {"P": 0.5}})
    assert satisfies_fuzzy_modal(MODAL.parse(K_AXIOM), by_hand, 0) == 0.5
    assert_countermodel(search(K_AXIOM), K_AXIOM, worlds=1)


def test_the_axiom_k_holds_over_a_crisp_frame_and_under_goedel():
    """A weight 0 makes every term 1, and at weight 1 the axiom is ``(a → b) ⊗ a ≤ b``.
    Under Gödel ``(r → (a → b)) ∧ (r → a) = r → ((a → b) ∧ a) ≤ r → b`` for every ``r``."""
    assert_none_up_to(search(K_AXIOM, crisp_frame=True))
    assert_none_up_to(search(K_AXIOM, tnorm=G))


def test_a_crisp_frame_has_weights_zero_and_one():
    result = search("□P → P", crisp_frame=True)
    assert_countermodel(result, "□P → P", worlds=1)
    weights = {w for edges in result.model.relations.values() for w in edges.values()}
    assert weights <= {0.0, 1.0}


# ---------------------------------------------------------------------------
# Frame conditions in their graded form
# ---------------------------------------------------------------------------

# (axiom, frame under which it has degree 1, size of the smallest countermodel in K)
#
# T  □P → P: one world that does not see itself has □P = 1 and P = 0.
# D  □P → ◇P: the same world, □P = 1 and ◇P = 0.
# 4  □P → □□P: in one world □□P = (r ⊗ r) → p ≥ r → p = □P, so two worlds are needed:
#    0 and 1 see each other with weight 1, P is 1 at 1 and 0 at 0; □P = 1 and □□P = 0 at 0.
# B  P → □◇P: in one world □◇P = r → (r ⊗ p) ≥ p; with two worlds, 0 sees 1 and 1 sees
#    nothing: ◇P = 0 at 1, so □◇P = 0 at 0, while P = 1 there.
# 5  ◇P → □◇P: in one world □◇P = r → (r ⊗ p) ≥ r ⊗ p = ◇P; with two worlds, 0 sees 0
#    and 1 with weight 1, 1 sees nothing, P = 1 at 0: ◇P = 1 at 0 and 0 at 1.
AXIOMS = [
    ("□P → P", "T", 1),
    ("□P → ◇P", "KD", 1),
    ("□P → □□P", "K4", 2),
    ("P → □◇P", "KB", 2),
    ("◇P → □◇P", "K5", 2),
]


@pytest.mark.parametrize("axiom, frame, size", AXIOMS)
@pytest.mark.parametrize("tnorm", [L, G])
def test_an_axiom_has_a_countermodel_in_k_and_none_in_its_frame(tnorm, axiom, frame, size):
    assert_countermodel(search(axiom, tnorm=tnorm), axiom, worlds=size)
    assert_none_up_to(search(axiom, tnorm=tnorm, frame=frame))


@pytest.mark.parametrize("tnorm", [L, G])
def test_s5_has_every_one_of_them(tnorm):
    for axiom, _, _ in AXIOMS:
        assert_none_up_to(search(axiom, tnorm=tnorm, frame="S5"))


def test_transitivity_is_read_with_the_tnorm():
    """``R(0, 1) = R(1, 0) = 1/2`` and no loop is transitive under Łukasiewicz
    (``1/2 ⊗ 1/2 = 0``) and not under Gödel (``min = 1/2 > R(0, 0)``)."""
    model = FuzzyKripkeModel({0, 1}, {"alethic": {(0, 1): 0.5, (1, 0): 0.5}},
                             {0: {"P": 0.0}, 1: {"P": 1.0}})
    # □P = 1/2 → 1 = 1 at 0; □P = 1/2 → 0 = 1/2 at 1; □□P = 1/2 → 1/2 = 1 at 0
    assert satisfies_fuzzy_modal(MODAL.parse("□P → □□P"), model, 0) == 1.0
    # Gödel: □P = 0 at 1 and □□P = 1/2 → 0 = 0 at 0: this model refutes 4, and is not K4
    assert satisfies_fuzzy_modal(
        MODAL.parse("□P → □□P"),
        FuzzyKripkeModel(model.worlds, model.relations, model.valuation, tnorm=GODEL), 0) == 0.0
    assert_none_up_to(search("□P → □□P", tnorm=G, frame="K4"))


def test_the_frames_of_the_agents_are_given_by_family():
    assert_countermodel(search("K_alice P → P"), "K_alice P → P", worlds=1)
    assert_none_up_to(search("K_alice P → P", systems={"epistemic": "T"}))
    assert_none_up_to(search("K_alice P → K_alice K_alice P", systems={"epistemic": "S5"}))
    # the frame of □ is not the frame of an agent, and the frame of knowledge not that of belief
    assert_countermodel(search("K_alice P → P", frame="S5"), "K_alice P → P")
    assert_countermodel(search("B_alice P → P", systems={"epistemic": "S5"}), "B_alice P → P")
    assert_none_up_to(search("B_alice P → ¬B_alice ¬P", systems={"doxastic": "KD45"}))
    # Says has no frame condition
    assert_countermodel(search("Say_alice P → P", systems={"epistemic": "S5"}), "Say_alice P → P")


def test_an_unknown_frame_a_frame_without_a_graded_form_and_an_unknown_family():
    with pytest.raises(ValueError, match="fuzzy_modal_search"):
        search("□P", frame="NoSuchFrame")
    with pytest.raises(NotImplementedError, match="graded form of refl, sym, trans, serial, eucl"):
        search("□P", frame="GL")
    with pytest.raises(ValueError, match="unknown system family 'deontic'"):
        search("□P", systems={"deontic": "KD"})
    with pytest.raises(ValueError, match="max_worlds must be at least 1"):
        search("□P", max_worlds=0)
    with pytest.raises(NotImplementedError, match="product"):
        search("□P", tnorm="product")
    with pytest.raises(ValueError, match="unknown t-norm"):
        search("□P", tnorm="minimum")


# ---------------------------------------------------------------------------
# No countermodel up to a bound is not validity
# ---------------------------------------------------------------------------

def test_a_goedel_formula_without_a_finite_countermodel():
    """``□¬¬P → ¬¬□P`` has degree 1 in every finite Gödel model: if ``¬¬□P = 0`` then
    ``□P = 0``, so some ``v`` has ``R(w, v) > P(v) = 0``, and then ``R(w, v) → ¬¬P(v) = 0``
    makes ``□¬¬P = 0``. Over infinitely many worlds with ``P = 1/n`` at the n-th it has
    degree 0: every ``¬¬P`` is 1 and the infimum of ``P`` is 0. The search reports the
    first and cannot see the second."""
    result = search("□¬¬P → ¬¬□P", tnorm=G, max_worlds=4)
    assert_none_up_to(result, 4)
    # a finite piece of that model: □P is the least of the degrees, above 0
    worlds = range(6)
    piece = FuzzyKripkeModel(
        worlds, {"alethic": {(0, n): 1.0 for n in worlds if n}},
        {n: {"P": 1.0 / n} for n in worlds if n}, tnorm=GODEL)
    assert satisfies_fuzzy_modal(MODAL.parse("□P"), piece, 0) == 0.2
    assert satisfies_fuzzy_modal(MODAL.parse("□¬¬P → ¬¬□P"), piece, 0) == 1.0


@pytest.mark.parametrize("text, options", [
    ("□(P → Q) → (□P → □Q)", {"tnorm": G}),
    ("□(P ∧ Q) ↔ (□P ∧ □Q)", {}),
    ("◇(P ∨ Q) ↔ (◇P ∨ ◇Q)", {}),
    ("□P → □□P", {"frame": "S4"}),
    ("P → □◇P", {"frame": "S5", "tnorm": G}),
    ("K_alice (P ∧ Q) → K_alice P", {}),
])
def test_no_model_up_to_the_bound_gives_a_reported_formula_a_degree_below_one(text, options):
    """An independent look at ``exhausted``: random models of the frame class, with up to
    three worlds, all give the formula degree 1 at world 0."""
    assert_none_up_to(search(text, **options))
    tnorm = GODEL if options.get("tnorm") == G else LUKASIEWICZ
    frame = options.get("frame", "K")
    rng = random.Random(33)
    eighths = [k / 8 for k in range(9)]
    formula = MODAL.parse(text)
    for _ in range(150):
        worlds = range(rng.randint(1, 3))
        if frame == "K":
            edges = {(w, v): rng.choice(eighths) for w in worlds for v in worlds}
        else:
            # an equivalence relation with weight 1 inside a class: reflexive, symmetric,
            # transitive under either t-norm
            block = {w: rng.randrange(2) for w in worlds}
            edges = {(w, v): 1.0 for w in worlds for v in worlds if block[w] == block[v]}
        model = FuzzyKripkeModel(
            worlds, {"alethic": edges, "K:alice": edges},
            {w: {"P": rng.choice(eighths), "Q": rng.choice(eighths)} for w in worlds},
            tnorm=tnorm)
        assert satisfies_fuzzy_modal(formula, model, 0) == 1.0


# ---------------------------------------------------------------------------
# Quantifiers
# ---------------------------------------------------------------------------

def test_the_barcan_formulas_hold_over_a_constant_domain():
    """``inf over v of (r → min over x of P(x))`` and ``min over x of inf over v of (r → P(x))``
    are one number: ``r → ·`` commutes with a minimum."""
    for text in ("∀x □P(x) → □∀x P(x)", "□∀x P(x) → ∀x □P(x)", "∃x □P(x) → □∃x P(x)"):
        assert_none_up_to(search(text, domain=D))
    # □∃x P(x) → ∃x □P(x) fails with two worlds: 0 sees 0 and 1, P is of alice at 0 and
    # of bob at 1. With one world both sides are r → max(P(alice), P(bob)).
    result = search("□∃x P(x) → ∃x □P(x)", domain=D)
    assert_countermodel(result, "□∃x P(x) → ∃x □P(x)", worlds=2)
    assert result.model.domain == frozenset(D)


def test_sorted_individuals_in_the_search():
    universes = {"Human": {"alice"}, "Being": D}
    result = fuzzy_modal_search(
        SORTED.parse("∀x:Being □P(x) → □∀x:Human P(x)"), sort_universes=universes)
    assert_none_up_to(result)
    result = fuzzy_modal_search(
        SORTED.parse("∀x:Human □P(x) → □∀x:Being P(x)"), sort_universes=universes)
    assert result.model is not None and result.degree < 1.0
    assert result.model.sort_universes == {"Human": frozenset({"alice"}), "Being": frozenset(D)}


def test_a_quantifier_without_its_universe_is_reported():
    result = search("∀x □P(x)")
    assert result.model is None and not result.exhausted
    assert result.unsupported.startswith("ValueError: fuzzy_modal_search: the quantifier ∀x")


@pytest.mark.parametrize("tnorm", [L, G])
def test_correspondence_in_the_object_language(tnorm):
    """``∀P (□P → P)`` has the degree of the loop at world 0, so it has a countermodel in K
    and none over reflexive frames; ``∀P (□P → □□P)`` likewise for transitive ones."""
    assert_countermodel(search("∀P (□P → P)", SO, tnorm=tnorm), "∀P (□P → P)", SO, worlds=1)
    assert_none_up_to(search("∀P (□P → P)", SO, tnorm=tnorm, frame="T"))
    assert_countermodel(search("∀P (□P → □□P)", SO, tnorm=tnorm), "∀P (□P → □□P)", SO)
    assert_none_up_to(search("∀P (□P → □□P)", SO, tnorm=tnorm, frame="K4"))


def test_the_model_of_a_predicate_quantifier_holds_no_bound_atom():
    result = search("∀P (□P → P)", SO)
    assert all(not degrees for degrees in result.model.valuation.values())


def test_a_predicate_quantifier_below_the_root():
    """``Q → ∀P (□P → P)``: ``Q = 1`` at a world that does not see itself."""
    result = search("Q → ∀P (□P → P)", SO, max_worlds=1)
    assert_countermodel(result, "Q → ∀P (□P → P)", SO, worlds=1)
    assert_none_up_to(search("Q → ∀P (□P → P)", SO, frame="T", max_worlds=1), 1)


def test_bound_predicates_over_two_terms_need_the_names_declared():
    text = "∃P (P(alice) ⊗ ¬P(bob))"
    result = search(text, SO)
    assert result.model is None and not result.exhausted and result.worlds == 0
    assert result.unsupported.startswith("NotImplementedError: fuzzy_modal_search: predicate")
    assert "may name one individual" in result.unsupported
    assert_none_up_to(search(text, SO, domain=D))


def test_a_third_order_atom_is_a_letter_in_the_search():
    assert_none_up_to(search("□(Pos(G) ∧ Pos(H)) → □Pos(G)", TO))
    assert_countermodel(search("Pos(G) → □Pos(G)", TO), "Pos(G) → □Pos(G)", TO)
    result = search("∀G (Pos(G) → □Pos(G))", TO)
    assert result.unsupported.startswith("NotImplementedError") and "argument position" in result.unsupported


@pytest.mark.parametrize("text, family", [
    ("ⒼP", "temporal"), ("P Ⓤ Q", "temporal"), ("@i P", "hybrid"), ("p → □p", "hybrid"),
    ("[P!]Q", "public announcement logic"), ("ⓄP → ⓅP", "deontic"),
])
def test_an_operator_outside_the_graded_semantics_is_reported(text, family):
    result = search(text)
    assert result.model is None and not result.exhausted and not result.timed_out
    assert result.unsupported.startswith("NotImplementedError: fuzzy_modal_search:")
    assert f"({family})" in result.unsupported


def test_a_free_variable_next_to_a_quantifier_is_reported():
    result = search("∀y (□P(y) → P(x))", domain=D)
    assert "free in a quantified formula" in result.unsupported


# ---------------------------------------------------------------------------
# The result
# ---------------------------------------------------------------------------

def test_a_countermodel_is_reported_with_a_wide_margin_where_there_is_one():
    """``□P → P`` can have degree 0, so the model reported is not one with degree 0.999."""
    assert search("□P → P").degree <= 0.5


def test_the_convenience_function_returns_the_model_alone():
    model = fuzzy_modal_countermodel(MODAL.parse("□P → P"))
    assert isinstance(model, FuzzyKripkeModel)
    assert satisfies_fuzzy_modal(MODAL.parse("□P → P"), model, 0) < 1.0
    assert fuzzy_modal_countermodel(MODAL.parse("□P → P"), frame="T") is None
    assert fuzzy_modal_countermodel(MODAL.parse("ⒼP")) is None


@pytest.mark.parametrize("text, options", [
    ("□P → P", {}),
    ("□∃x P(x) → ∃x □P(x)", {"domain": D}),
    ("K_alice P → B_alice P", {"tnorm": G}),
])
def test_a_result_and_its_model_are_json(text, options):
    result = search(text, **options)
    data = json.loads(json.dumps(result.to_dict()))
    assert data["found"] is True and data["degree"] == result.degree
    assert data["exhausted"] is False and data["timed_out"] is False
    rebuilt = fuzzy_kripke_model_from_dict(data["model"])
    assert fuzzy_kripke_model_to_dict(rebuilt) == data["model"]
    assert rebuilt.tnorm is result.model.tnorm and rebuilt.domain == result.model.domain
    assert satisfies_fuzzy_modal(MODAL.parse(text), rebuilt, 0) == result.degree


def test_a_result_without_a_model_is_json():
    data = json.loads(json.dumps(search("□P → P", frame="T").to_dict()))
    assert data == {"found": False, "degree": None, "exhausted": True, "worlds": 3,
                    "unsupported": None, "timed_out": False, "model": None,
                    "detail": "no countermodel with at most 3 world(s); not a proof of "
                              "validity, larger models are not searched"}


def test_the_dict_of_a_model_leaves_out_what_reads_as_zero():
    model = FuzzyKripkeModel(
        {0, 1}, {"alethic": {(0, 1): 0.5, (1, 0): 0.0}}, {0: {"P": 0.0, "Q": 0.25}},
        tnorm=GODEL, domain=["bob", "alice"], sort_universes={"S": ["bob"]})
    assert fuzzy_kripke_model_to_dict(model) == {
        "worlds": [0, 1],
        "relations": {"alethic": [[0, 1, 0.5]]},
        "valuation": {"0": {"Q": 0.25}},
        "tnorm": "godel",
        "domain": ["alice", "bob"],
        "sort_universes": {"S": ["bob"]},
    }


class Undecided(z3.Solver):
    """A solver that decides its first ``decides`` problems and gives up on the rest."""

    decides = 0
    asked = 0

    def check(self, *assumptions):
        type(self).asked += 1
        if type(self).asked > type(self).decides:
            return z3.unknown
        return super().check(*assumptions)


def test_a_size_z3_does_not_decide_is_reported_as_such(monkeypatch):
    monkeypatch.setattr(z3_fuzzy_kripke, "Solver", Undecided)
    monkeypatch.setattr(Undecided, "decides", 0)
    monkeypatch.setattr(Undecided, "asked", 0)
    result = search("□P → □□P")
    assert isinstance(result, FuzzyModalSearchResult)
    assert result.timed_out and result.model is None and not result.exhausted
    assert result.worlds == 0
    assert "did not decide the models with 1 world(s)" in result.detail


def test_the_sizes_decided_before_are_counted(monkeypatch):
    """``□P → □□P`` has no countermodel with one world; the second size is not decided."""
    monkeypatch.setattr(z3_fuzzy_kripke, "Solver", Undecided)
    monkeypatch.setattr(Undecided, "decides", 1)
    monkeypatch.setattr(Undecided, "asked", 0)
    result = search("□P → □□P")
    assert result.timed_out and not result.exhausted and result.worlds == 1
    assert "did not decide the models with 2 world(s)" in result.detail


def test_a_model_that_is_none_in_floats_is_not_reported(monkeypatch):
    """The search computes the degree of what Z3 found again, with the evaluator, and
    reports no model whose degree is not below 1 there."""
    monkeypatch.setattr(z3_fuzzy_kripke, "satisfies_fuzzy_modal", lambda *args: 1.0)
    result = search("□P → P")
    assert result.model is None and result.degree is None and not result.exhausted
    assert "not below 1" in result.detail


# ---------------------------------------------------------------------------
# The two-valued routes
# ---------------------------------------------------------------------------

def test_a_two_valued_modal_route_refuses_a_fuzzy_formula_and_names_the_fuzzy_ones():
    from unicode_logic_kit import (
        KripkeModel, modal_enum_search, qml_is_valid, satisfies_modal, standard_translation,
    )
    node = MODAL.parse("□(P ⊗ Q) → □P")
    with pytest.raises(NotImplementedError, match="satisfies_fuzzy_modal"):
        satisfies_modal(node, KripkeModel(worlds={0}), 0)
    with pytest.raises(NotImplementedError, match="fuzzy_modal_search"):
        standard_translation(node)
    assert "this route is two-valued" in modal_enum_search(node).unsupported
    with pytest.raises(RuntimeError, match="reached a two-valued route"):
        qml_is_valid(node)


def test_the_search_is_exported_at_the_top_level():
    import unicode_logic_kit
    from unicode_logic_kit import atp

    for name in ("FuzzyModalSearchResult", "fuzzy_modal_search", "fuzzy_modal_countermodel",
                 "fuzzy_kripke_model_to_dict", "fuzzy_kripke_model_from_dict"):
        assert getattr(unicode_logic_kit, name) is getattr(z3_fuzzy_kripke, name)
        assert name in unicode_logic_kit.__all__ and name in atp.__all__


def test_the_individuals_may_be_given_as_any_iterable():
    """The domain is read once, also when the search goes through several sizes."""
    result = fuzzy_modal_search(
        MODAL.parse("□∃x P(x) → ∃x □P(x)"), domain=(name for name in ("alice", "bob")),
        sort_universes={"S": iter(["carol"])})
    assert_countermodel(result, "□∃x P(x) → ∃x □P(x)", worlds=2)
    assert result.model.domain == frozenset(D)
    assert result.model.sort_universes == {"S": frozenset({"carol"})}
