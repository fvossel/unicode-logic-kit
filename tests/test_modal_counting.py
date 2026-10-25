"""Counting quantifiers and Contrast in the modal routes.

A node that the classical layer defines by other nodes is read by that definition in
every modal embedding: ``∃≥n`` / ``∃≤n`` / ``∃=n`` (sorted or not) by its distinct
witnesses, which are object quantifiers under the route's domain regime and whose
distinctness is rigid identity, and ``Contrast`` as ``∧``. The Kripke evaluator counts
the individuals of the world's domain. Every expected verdict below is derived by hand.
"""
import pytest

from unicode_logic_kit.fol import qml
from unicode_logic_kit.fol.modal_translation import standard_translation
from unicode_logic_kit.fol.msflparser import MSFLParser
from unicode_logic_kit.fol.nodes import And, Atom, Constant, Contrast, Count, Diamond
from unicode_logic_kit.hol.isabelle_modal import to_isabelle_modal
from unicode_logic_kit.hol.thf_modal import to_thf_modal_full
from unicode_logic_kit.semantics.kripke import KripkeModel, satisfies_modal

MODAL = MSFLParser(modal=True)
SORTED = MSFLParser(modal=True, many_sorted=True)
SECOND_ORDER = MSFLParser(modal=True, second_order=True)

A = Constant("a")


def _contrast(left, right):
    return Diamond(Contrast(Atom(left, (A,)), Atom(right, (A,))))


def _conjunction(left, right):
    return Diamond(And(Atom(left, (A,)), Atom(right, (A,))))


# --------------------------------------------------------------------------- #
# Every embedding reads a count by its definition.
# --------------------------------------------------------------------------- #

#: A count and its distinct-witnesses definition, written out by hand. The witnesses
#: are named like the counting variable and avoid every name of the matrix:
#: ∃≥m is ∃x0 … ∃x{m-1} (⋀ φ(x_i) ∧ ⋀ x_i ≠ x_j), ∃≤n is ¬∃≥n+1, ∃=n is ∃≥n ∧ ¬∃≥n+1.
DEFINITIONS = [
    ("◇∃≥2 x P(x)", "◇∃x0 ∃x1 (P(x0) ∧ P(x1) ∧ x0 ≠ x1)"),
    ("□∃=1 x P(x)", "□(∃x0 P(x0) ∧ ¬∃x1 ∃x2 (P(x1) ∧ P(x2) ∧ x1 ≠ x2))"),
    ("◇∃≤1 x0 Q(x0, x1)", "◇¬∃x2 ∃x3 (Q(x2, x1) ∧ Q(x3, x1) ∧ x2 ≠ x3)"),
]

EMBEDDINGS = {
    "qml_translate": qml.qml_translate,
    "qml_validity_formula": lambda f: qml.qml_validity_formula(f, mode="varying", frame="T"),
    "to_thf_modal": qml.to_thf_modal,
    "to_thf_modal_full": to_thf_modal_full,
    "to_isabelle_modal": to_isabelle_modal,
}


@pytest.mark.parametrize("route", EMBEDDINGS.values(), ids=EMBEDDINGS.keys())
@pytest.mark.parametrize("counted, defined", DEFINITIONS, ids=[d[0] for d in DEFINITIONS])
def test_each_embedding_reads_a_count_by_its_definition(route, counted, defined):
    assert route(MODAL.parse(counted)) == route(MODAL.parse(defined))


@pytest.mark.parametrize("route", EMBEDDINGS.values(), ids=EMBEDDINGS.keys())
def test_each_embedding_reads_contrast_as_conjunction(route):
    assert route(_contrast("P", "Q")) == route(_conjunction("P", "Q"))


def test_a_count_is_translated_with_the_guard_of_the_regime():
    # ∃≥1 x P(x) is ∃x0 P(x0); the witness is an object, and under an actualist
    # regime one that exists at the world of evaluation
    counted = MODAL.parse("∃≥1 x P(x)")
    assert qml.qml_translate(counted).to_unicode_str() == "∃x0 (Object(x0) ∧ P(x0, w))"
    assert (qml.qml_translate(counted, mode="varying").to_unicode_str()
            == "∃x0 (Object(x0) ∧ E(x0, w) ∧ P(x0, w))")


def test_the_formulas_of_the_request_translate():
    example = MODAL.parse("◇(∃=1 x0((Wug(x0) ∧ Near(korra, x0))))")
    premise = MODAL.parse(
        "∀x0((City(x0) → (((((For(x0, bristol) ∧ For(x0, texarkana)) ∧ For(x0, texhoma)) "
        "∧ For(x0, unioncity)) ∧ ¬(◇(∃=1 x1(((State(x1) ∧ In(x1, us)) ∧ In(x0, x1)))))) "
        "∨ ◇(∃=1 x2(((State(x2) ∧ In(x2, us)) ∧ In(x0, x2)))))))")
    for formula in (example, premise):
        query = qml.qml_validity_formula(formula, mode="constant", frame="T")
        assert not any(isinstance(node, Count) for node in query.walk())


# --------------------------------------------------------------------------- #
# What the definition means: verdicts derived by hand, decided by Z3.
# --------------------------------------------------------------------------- #

MODES = ["constant", "increasing", "varying", "decreasing"]


@pytest.mark.parametrize("mode", MODES)
def test_exactly_one_is_some_and_only_that_one(mode):
    # the reading the request names: ∃=1 x φ is ∃x (φ(x) ∧ ∀y (φ(y) → y = x)), at
    # every world and under every regime, since both sides quantify over one domain
    assert qml.qml_equivalent(MODAL.parse("◇∃=1 x P(x)"),
                              MODAL.parse("◇∃x (P(x) ∧ ∀y (P(y) → y = x))"), mode=mode)
    assert qml.qml_equivalent(MODAL.parse("∃≤0 x P(x)"), MODAL.parse("¬∃x P(x)"), mode=mode)


@pytest.mark.parametrize("mode, valid", [
    ("constant", True), ("increasing", True), ("varying", False), ("decreasing", False)])
def test_distinctness_is_rigid_and_the_witnesses_follow_the_regime(mode, valid):
    # two distinct objects that are P at every successor are two distinct P there,
    # if they are in the successor's domain: so under constant and increasing domains
    # only
    formula = MODAL.parse("∃≥2 x □P(x) → □∃≥2 x P(x)")
    assert qml.qml_is_valid(formula, mode=mode) is valid


@pytest.mark.parametrize("frame, valid", [("T", True), ("K", False)])
def test_a_necessary_count_holds_where_the_frame_is_reflexive(frame, valid):
    assert qml.qml_is_valid(MODAL.parse("□∃=1 x P(x) → ∃=1 x P(x)"), frame=frame) is valid


def test_a_sorted_count_counts_the_members_of_its_sort():
    assert qml.qml_equivalent(SORTED.parse("◇∃=1 x:S P(x)"),
                              SORTED.parse("◇∃x:S (P(x) ∧ ∀y:S (P(y) → y = x))"))


def test_the_premise_of_the_request_gives_its_second_disjunct():
    # a city that is not For(·, bristol) fails the first disjunct, so the second holds
    premise = ("∀x0((City(x0) → (((((For(x0, bristol) ∧ For(x0, texarkana)) ∧ For(x0, texhoma)) "
               "∧ For(x0, unioncity)) ∧ ¬(◇(∃=1 x1(((State(x1) ∧ In(x1, us)) ∧ In(x0, x1)))))) "
               "∨ ◇(∃=1 x2(((State(x2) ∧ In(x2, us)) ∧ In(x0, x2)))))))")
    formula = MODAL.parse(
        f"({premise} ∧ City(springfield) ∧ ¬For(springfield, bristol)) → "
        f"◇∃=1 x (State(x) ∧ In(x, us) ∧ In(springfield, x))")
    assert qml.qml_is_valid(formula, frame="K")


# --------------------------------------------------------------------------- #
# The propositional standard translation and the Kripke evaluator.
# --------------------------------------------------------------------------- #

def test_the_standard_translation_reads_contrast_and_refuses_a_count_as_a_quantifier():
    assert standard_translation(_contrast("P", "Q")) == standard_translation(_conjunction("P", "Q"))
    with pytest.raises(NotImplementedError, match="Quantifier is not supported"):
        standard_translation(MODAL.parse("◇∃=1 x P(x)"))


#: World 0 holds a, b and c with P(a), P(b) and S(a); world 1, reached from 0, holds a
#: alone with P(a); world 2, reached from 1, has an empty domain.
MODEL = KripkeModel(
    worlds={0, 1, 2}, relations={"alethic": {(0, 1), (1, 2)}},
    valuation={0: {"P(a)", "P(b)", "S(a)"}, 1: {"P(a)"}, 2: set()},
    domains={0: {"a", "b", "c"}, 1: {"a"}, 2: set()})


@pytest.mark.parametrize("text, world, holds", [
    ("∃=2 x P(x)", 0, True),
    ("∃≥3 x P(x)", 0, False),
    ("∃≤1 x P(x)", 0, False),
    ("∃=0 x Q(x)", 0, True),
    ("◇∃=1 x P(x)", 0, True),
    ("□∃=2 x P(x)", 0, False),
    # an empty domain: no individual satisfies anything, and zero is at most zero
    ("∃=0 x P(x)", 2, True),
    ("∃≥0 x P(x)", 2, True),
    ("∃≥1 x P(x)", 2, False),
])
def test_the_evaluator_counts_the_individuals_of_the_world(text, world, holds):
    assert satisfies_modal(MODAL.parse(text), MODEL, world) is holds


def test_the_evaluator_reads_a_sorted_count_and_contrast():
    assert satisfies_modal(SORTED.parse("∃=1 x:S P(x)"), MODEL, 0) is True
    assert satisfies_modal(Contrast(Atom("P", (A,)), Atom("P", (Constant("b"),))), MODEL, 0) is True
    assert satisfies_modal(Contrast(Atom("P", (A,)), Atom("P", (Constant("c"),))), MODEL, 0) is False


def test_a_predicate_quantifier_reaches_the_individuals_a_count_binds():
    # P can be made true of exactly two of a, b, c only if the interpretations of the
    # bound P give it an extension over the individuals the count ranges over
    assert satisfies_modal(SECOND_ORDER.parse("∃P ∃=2 x P(x)"), MODEL, 0) is True
    assert satisfies_modal(SECOND_ORDER.parse("∃P ∃=4 x P(x)"), MODEL, 0) is False
