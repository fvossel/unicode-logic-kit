"""The fuzzy parser modes are the same three choices as the classical ones.

A fuzzy mode is fixed by the order (first, second, third), by whether the modal family
is there, and by whether the individual binders and constants carry sorts: twelve
modes, of which ``fl`` and ``msfl`` are the first-order ones without the modal family.
A fuzzy mode differs from the classical mode of the same three choices in its
connectives and in nothing else:

    classical          fuzzy
    ¬  Not             LukNegation
    ∧  And             WeakConjunction
    ∨  Or              WeakDisjunction
    →  Implies         LukImplication
    ↔  Iff             LukEquivalence
    ⊕  Xor             StrongDisjunction
    ⊗  (none)          StrongConjunction

and it has none of the forms whose reading is two-valued: the counting quantifier,
``but``, the measure term and the cardinality term.

So the tests state two rules and check them for every mode. A formula over
``¬ ∧ ∨ → ↔`` is read by a fuzzy mode as the classical mode of the same choices reads
it, connective for connective. And a formula that uses the features ``(order, modal,
sorted)`` is accepted by the fuzzy mode ``(order', modal', sorted')`` exactly when
``order <= order'``, the modal family is there if the formula needs it, and
``sorted == sorted'``.
"""

import itertools

import pytest

from unicode_logic_kit import MSFLParser, MixedSlotError
from unicode_logic_kit.fol._fol_nodes import build_grammar, parser_ops_for_mode
from unicode_logic_kit.fol.msflparser import _REGISTRY_MODE
from unicode_logic_kit.fol.naming import NamingError, ParsingError
from unicode_logic_kit.fol.nodes import (
    And, Atom, Box, Constant, Diamond, Iff, Implies, Knows, Lambda, LambdaVar, LukEquivalence,
    LukImplication, LukNegation, Nominal, Not, Or, PredicateTerm, Quantifier,
    SecondOrderQuantifier, SortedConstant, SortedQuantifier, StrongConjunction,
    StrongDisjunction, Variable, WeakConjunction, WeakDisjunction,
)
from unicode_logic_kit.fol._so_nodes import ConflictingArityError

#: (order, modal, sorted) -> the name the parser gives the fuzzy mode.
MODE_NAMES = {
    (1, False, False): "fl",
    (1, False, True): "msfl",
    (1, True, False): "flmodal",
    (1, True, True): "flmodal_sorted",
    (2, False, False): "flso",
    (2, False, True): "flso_sorted",
    (2, True, False): "flsomodal",
    (2, True, True): "flsomodal_sorted",
    (3, False, False): "flto",
    (3, False, True): "flto_sorted",
    (3, True, False): "fltomodal",
    (3, True, True): "fltomodal_sorted",
}
COMBINATIONS = sorted(MODE_NAMES)

#: The classical connective and the fuzzy node the same glyph builds.
FUZZY_NODE = {Not: LukNegation, And: WeakConjunction, Or: WeakDisjunction,
              Implies: LukImplication, Iff: LukEquivalence}


def flags(order, modal, many_sorted, fuzzy=True):
    kwargs = {"fuzzy": True} if fuzzy else {}
    if order == 2:
        kwargs["second_order"] = True
    if order == 3:
        kwargs["third_order"] = True
    if modal:
        kwargs["modal"] = True
    if many_sorted:
        kwargs["many_sorted"] = True
    return kwargs


def parser(order, modal, many_sorted, fuzzy=True):
    return MSFLParser(**flags(order, modal, many_sorted, fuzzy))


def fuzzified(node):
    """``node`` with every classical connective replaced by the fuzzy node of its glyph."""
    replaced = node.map_children(fuzzified)
    target = FUZZY_NODE.get(type(replaced))
    if target is None:
        return replaced
    if target is LukNegation:
        return LukNegation(replaced.formula)
    return target(replaced.left, replaced.right)


def witness(order, modal, many_sorted):
    """A formula that uses every feature of the combination, and no other."""
    parts = ["(∀x:S Q(x))" if many_sorted else "(∀x Q(x))"]
    if order >= 2:
        parts.append("(∃P P)")
    if order == 3:
        parts.append("Pos(G)")
    if modal:
        parts.append("□R")
    return " ∧ ".join(parts)


# ---------------------------------------------------------------------------
# Twelve modes
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("combination", COMBINATIONS)
def test_the_twelve_combinations_are_twelve_modes(combination):
    assert parser(*combination)._mode == MODE_NAMES[combination]


def test_every_fuzzy_mode_has_a_grammar_of_its_own_name():
    assert set(MODE_NAMES.values()) <= set(_REGISTRY_MODE)
    assert len({_REGISTRY_MODE[name] for name in MODE_NAMES.values()}) == 12


def test_third_order_still_contains_second_order():
    for extra in ({}, {"modal": True}, {"many_sorted": True}):
        with pytest.raises(ValueError, match="already CONTAINS"):
            MSFLParser(fuzzy=True, third_order=True, second_order=True, **extra)


@pytest.mark.parametrize("standalone", ["dependence", "linear", "lambek"])
def test_the_standalone_logics_take_no_fuzzy_flag(standalone):
    with pytest.raises(ValueError, match="cannot be combined with any other mode"):
        MSFLParser(fuzzy=True, **{standalone: True})


@pytest.mark.parametrize("formula_of, mode", list(itertools.product(COMBINATIONS, COMBINATIONS)))
def test_a_mode_accepts_exactly_the_formulas_of_the_modes_it_contains(formula_of, mode):
    text = witness(*formula_of)
    order, modal, many_sorted = formula_of
    mode_order, mode_modal, mode_sorted = mode
    accepted = order <= mode_order and (mode_modal or not modal) and many_sorted == mode_sorted
    if accepted:
        node = parser(*mode).parse(text)
        assert node == parser(*formula_of).parse(text)
        assert node.to_unicode_str() == text.replace("(∀x:S Q(x))", "∀x:S Q(x)").replace(
            "(∀x Q(x))", "∀x Q(x)").replace("(∃P P)", "∃P P")
    else:
        with pytest.raises((NamingError, ParsingError)):
            parser(*mode).parse(text)


# ---------------------------------------------------------------------------
# Connective for connective
# ---------------------------------------------------------------------------

#: Texts over ¬ ∧ ∨ → ↔ and the features named; (order, modal) is the least mode.
SHARED_TEXTS = [
    (1, True, "□(P → ◇Q)"),
    (1, True, "K_a P → P"),
    (1, True, "B_b (P ∧ Q) → B_b P"),
    (1, True, "Ⓖ(P → ⒻQ)"),
    (1, True, "ⓃP ∧ (P Ⓤ Q)"),
    (1, True, "ⓄP → ⓅP"),
    (1, True, "@i (P ∧ ◇j)"),
    (1, True, "□∀x (P(x) → Q(x))"),
    (1, True, "∃x ◇Likes(x, bob)"),
    (1, True, "◇⊤ → ¬□⊥"),
    (1, True, "(p → q) ∨ ¬(p ∧ q)"),
    (1, True, "[P!]Q ↔ (P → Q)"),
    (2, False, "∀P (P ∨ ¬P)"),
    (2, False, "∃P ∀x (P(x) ↔ Q(x))"),
    (2, False, "∀P (P(alice) → P(bob))"),
    (2, False, "∀x ∃P (P(x) ∧ ∀y (P(y) → Q(y, x)))"),
    (2, False, "(∀P P(alice)) ∧ (∃R R(alice, bob))"),
    (2, True, "∀P (□P → P)"),
    (2, True, "∀P (□P → □□P)"),
    (2, True, "∃P □◇K_a P(x, y)"),
    (3, False, "Pos(G) → ¬Pos(λx. ¬G(x))"),
    (3, False, "∀G (Pos(G) → ∃x G(x))"),
    (3, False, "∀x (Ess(G, x) ↔ (G(x) ∧ ∀H (H(x) → Nec(G, H))))"),
    (3, True, "∀G (Pos(G) → □Pos(G))"),
    (3, True, "∃x ∀G (Pos(G) → G(x)) → □∃x ∀G (Pos(G) → G(x))"),
]


@pytest.mark.parametrize("order, modal, text", SHARED_TEXTS)
def test_a_fuzzy_mode_reads_a_formula_as_the_classical_mode_does(order, modal, text):
    """Every mode that contains the text reads it; the fuzzy tree is the classical one
    with the fuzzy node at each connective."""
    for mode_order, mode_modal in itertools.product((1, 2, 3), (False, True)):
        if mode_order < order or (modal and not mode_modal):
            continue
        classical = parser(mode_order, mode_modal, False, fuzzy=False).parse(text)
        fuzzy = parser(mode_order, mode_modal, False).parse(text)
        assert fuzzy == fuzzified(classical)
        # a connective prints the same glyph for either node
        assert fuzzy.to_unicode_str() == classical.to_unicode_str()
        assert parser(mode_order, mode_modal, False).parse(fuzzy.to_unicode_str()) == fuzzy


SORTED_TEXTS = [
    (1, True, "□∀x:Human (Mortal(x) → ◇Wise(x))"),
    (1, True, "K_a ∃x:Human Wise(x) → ∃x:Human K_a Wise(x)"),
    (1, True, "□Mortal(socrates:Human)"),
    (2, False, "∃P ∀x:Human (P(x) ↔ Mortal(x))"),
    (2, True, "∀P (□∀x:Human P(x) → ∀x:Human □P(x))"),
    (3, False, "∀x:Being (Ess(G, x) → G(x))"),
    (3, True, "∀G (Pos(G) → □∃x:Being G(x))"),
]


@pytest.mark.parametrize("order, modal, text", SORTED_TEXTS)
def test_a_sorted_fuzzy_mode_reads_a_formula_as_the_sorted_classical_mode_does(order, modal, text):
    for mode_order, mode_modal in itertools.product((1, 2, 3), (False, True)):
        if mode_order < order or (modal and not mode_modal):
            continue
        classical = parser(mode_order, mode_modal, True, fuzzy=False).parse(text)
        fuzzy = parser(mode_order, mode_modal, True).parse(text)
        assert fuzzy == fuzzified(classical)
        assert parser(mode_order, mode_modal, True).parse(fuzzy.to_unicode_str()) == fuzzy


# ---------------------------------------------------------------------------
# The connectives of a fuzzy mode
# ---------------------------------------------------------------------------

P, Q = Atom("P", []), Atom("Q", [])


@pytest.mark.parametrize("combination", COMBINATIONS)
def test_every_fuzzy_mode_has_the_seven_connectives(combination):
    p = parser(*combination)
    assert p.parse("¬P") == LukNegation(P)
    assert p.parse("P ∧ Q") == WeakConjunction(P, Q)
    assert p.parse("P ∨ Q") == WeakDisjunction(P, Q)
    assert p.parse("P ⊗ Q") == StrongConjunction(P, Q)
    assert p.parse("P ⊕ Q") == StrongDisjunction(P, Q)      # not exclusive or
    assert p.parse("P → Q") == LukImplication(P, Q)
    assert p.parse("P ↔ Q") == LukEquivalence(P, Q)


@pytest.mark.parametrize("combination", COMBINATIONS)
def test_the_four_connectives_of_one_level_do_not_mix_without_parentheses(combination):
    p = parser(*combination)
    for text in ("P ∧ Q ∨ R", "P ⊗ Q ⊕ R", "P ∧ Q ⊗ R", "P ∨ Q ⊕ R"):
        with pytest.raises(NamingError, match="weak conjunction"):
            p.parse(text)
    assert p.parse("P ⊗ Q ⊗ R") == StrongConjunction(StrongConjunction(P, Q), Atom("R", []))


@pytest.mark.parametrize("combination", COMBINATIONS)
def test_no_fuzzy_mode_has_a_form_with_a_two_valued_reading(combination):
    p = parser(*combination)
    sort = ":S" if combination[2] else ""
    for text in (f"∃≥2 x{sort} P(x)",                    # the counting quantifier
                 "P but Q",                              # contrast
                 f"μ(x, height{sort}) > μ(y, height{sort})",        # the measure term
                 f"|{{v{sort} : Votes(x, v)}}| > |{{v{sort} : Votes(y, v)}}|"):   # cardinality
        with pytest.raises((NamingError, ParsingError)):
            p.parse(text)


def aliases(registry_mode):
    return {op.rule_alias for op in parser_ops_for_mode(registry_mode)}


TWO_VALUED = {"not_", "and_", "or_", "xor_", "implies_", "iff_", "contrast_", "count_"}


@pytest.mark.parametrize("combination", COMBINATIONS)
def test_a_fuzzy_mode_is_its_classical_mode_with_the_connectives_exchanged(combination):
    """The operators of a fuzzy mode: those of "fl" / "msfl", and every operator of the
    classical mode that is no connective and no counting form."""
    order, modal, many_sorted = combination
    classical = _REGISTRY_MODE[parser(order, modal, many_sorted, fuzzy=False)._mode]
    fuzzy = _REGISTRY_MODE[MODE_NAMES[combination]]
    base = "msfl" if many_sorted else "fl"
    kept = aliases(classical) - TWO_VALUED - {
        "sorted_count_", "sorted_cardinality_"}
    assert aliases(fuzzy) == aliases(base) | kept
    assert not aliases(fuzzy) & TWO_VALUED
    assert ("hoarglist" in build_grammar(fuzzy)) == (order == 3)


# ---------------------------------------------------------------------------
# Sorts
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("order, modal", [(1, True), (2, False), (2, True), (3, False), (3, True)])
def test_a_sorted_fuzzy_mode_refuses_an_unsorted_binder_and_a_bare_constant(order, modal):
    p = parser(order, modal, True)
    assert p.parse("∀x:S P(x)") == SortedQuantifier("∀", Variable("x"), "S",
                                                    Atom("P", [Variable("x")]))
    assert p.parse("P(alice:S)") == Atom("P", [SortedConstant("alice", "S")])
    with pytest.raises(NamingError):
        p.parse("∀x P(x)")
    with pytest.raises((NamingError, ParsingError)):
        p.parse("P(alice)")


@pytest.mark.parametrize("order, modal", [(1, True), (2, False), (2, True), (3, False), (3, True)])
def test_an_unsorted_fuzzy_mode_has_no_sort_annotation(order, modal):
    p = parser(order, modal, False)
    assert p.parse("∀x P(x)") == Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
    with pytest.raises(NamingError):
        p.parse("∀x:S P(x)")


@pytest.mark.parametrize("modal", [False, True])
def test_a_predicate_quantifier_is_unsorted_in_a_sorted_mode(modal):
    node = parser(2, modal, True).parse("∃P ∀x:S (P(x) ↔ Q(x))")
    assert isinstance(node, SecondOrderQuantifier)
    assert (node.type, node.predicate, node.arity) == ("∃", "P", 1)
    assert isinstance(node.formula, SortedQuantifier) and node.formula.sort == "S"
    assert isinstance(node.formula.formula, LukEquivalence)


# ---------------------------------------------------------------------------
# The modal family
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("order", [1, 2, 3])
def test_the_modal_operators_stand_over_fuzzy_connectives(order):
    p = parser(order, True, False)
    assert p.parse("□(P ∧ Q) → □P") == LukImplication(Box(WeakConjunction(P, Q)), Box(P))
    assert p.parse("◇(P ⊗ Q)") == Diamond(StrongConjunction(P, Q))
    assert p.parse("K_alice P ⊕ ¬K_alice P") == StrongDisjunction(
        Knows(Constant("alice"), P), LukNegation(Knows(Constant("alice"), P)))


@pytest.mark.parametrize("order, many_sorted", itertools.product([1, 2, 3], [False, True]))
def test_a_bare_lower_case_word_is_a_nominal_in_a_modal_fuzzy_mode(order, many_sorted):
    """As in the classical modal modes, and it needs the same second parser: ``(p → q)``
    is the shape the first one misreads."""
    p = parser(order, True, many_sorted)
    assert p._hybrid
    assert p.parse("(p → q) ∧ p") == WeakConjunction(
        LukImplication(Nominal("p"), Nominal("q")), Nominal("p"))


@pytest.mark.parametrize("order, many_sorted", itertools.product([1, 2, 3], [False, True]))
def test_a_fuzzy_mode_without_the_modal_family_has_no_modal_operator(order, many_sorted):
    p = parser(order, False, many_sorted)
    assert not p._hybrid
    for text in ("□P", "◇P", "K_a P", "ⒼP", "@i P"):
        with pytest.raises((NamingError, ParsingError)):
            p.parse(text)
    with pytest.raises((NamingError, ParsingError)):
        p.parse("(p → q) ∧ p")


@pytest.mark.parametrize("order, many_sorted", itertools.product([1, 2, 3], [False, True]))
def test_a_free_agent_is_a_named_agent_and_a_bound_one_a_variable(order, many_sorted):
    p = parser(order, True, many_sorted)
    assert p.parse("K_a P") == Knows(Constant("a"), P)
    binder = "∀a:S" if many_sorted else "∀a"
    assert p.parse(f"{binder} K_a P").formula == Knows(Variable("a"), P)


@pytest.mark.parametrize("order", [2, 3])
def test_a_quantifier_sign_before_a_predicate_binds_the_predicate_in_a_modal_mode(order):
    """``∀ P(x)``: the predicate is bound and ``(x)`` is the nominal ``x`` in parentheses,
    as in the classical modal modes of the same order."""
    node = parser(order, True, False).parse("∀ P(x)")
    assert node == SecondOrderQuantifier("∀", "P", 0, Nominal("x"))
    with pytest.raises(ParsingError, match="Incomplete formula"):
        parser(order, False, False).parse("∀ P(x)")


# ---------------------------------------------------------------------------
# Second and third order
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("modal, many_sorted", itertools.product([False, True], repeat=2))
def test_the_arity_of_a_bound_predicate_is_read_from_its_body(modal, many_sorted):
    p = parser(2, modal, many_sorted)
    assert p.parse("∀P (P ⊗ P → P)").arity == 0
    assert p.parse("∀P (P(x) ⊗ P(y))").arity == 1
    assert p.parse("∃R (R(x, y) → R(y, x))").arity == 2
    with pytest.raises(ConflictingArityError):
        p.parse("∀P (P(x) → P(x, y))")


@pytest.mark.parametrize("modal, many_sorted", itertools.product([False, True], repeat=2))
def test_a_predicate_in_argument_position_is_third_order(modal, many_sorted):
    with pytest.raises(NamingError):
        parser(2, modal, many_sorted).parse("Pos(G)")
    assert parser(3, modal, many_sorted).parse("Pos(G)") == Atom("Pos", [PredicateTerm("G")])


@pytest.mark.parametrize("modal, many_sorted", itertools.product([False, True], repeat=2))
def test_a_lambda_term_in_argument_position_has_a_fuzzy_body(modal, many_sorted):
    node = parser(3, modal, many_sorted).parse("Pos(λx. ¬G(x))")
    assert node == Atom("Pos", [Lambda(LambdaVar("x"),
                                       LukNegation(Atom("G", [LambdaVar("x")])))])
    assert node.to_unicode_str() == "Pos(λx. ¬G(x))"


@pytest.mark.parametrize("modal, many_sorted", itertools.product([False, True], repeat=2))
def test_a_third_order_fuzzy_mode_types_its_argument_slots(modal, many_sorted):
    """One slot holds an individual or a property, as in the classical third-order modes."""
    individual = "alice:S" if many_sorted else "alice"
    with pytest.raises(MixedSlotError):
        parser(3, modal, many_sorted).parse(f"Pos(G) ∧ Pos({individual})")


@pytest.mark.parametrize("combination", COMBINATIONS)
def test_parse_with_spans_builds_the_tree_parse_builds(combination):
    p = parser(*combination)
    text = witness(*combination) + " → (A ⊗ ¬B)"
    spanned = p.parse_with_spans(text)
    assert spanned.formula == p.parse(text)
    assert spanned.spans.get(()).extent.text == text
