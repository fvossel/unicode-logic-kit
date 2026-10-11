"""Third-order atoms in the fuzzy routes: a letter, or a function of the caller.

``Pos(G)`` has a predicate in argument position. The fuzzy evaluator reads such an atom
in one of two ways. Without more it is a letter of its own, looked up by its written
form: the property is taken by NAME. With an entry for ``Pos`` in ``functionals`` it is
computed: the function receives the property as a function from constant names to
degrees. The deciders read the letter.
"""

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.z3_fuzzy import fuzzy_get_model, fuzzy_is_satisfiable, fuzzy_is_valid
from unicode_logic_kit.semantics.fuzzy import evaluate, ground_quantifiers

TO = MSFLParser(fuzzy=True, third_order=True)
TO_SORTED = MSFLParser(fuzzy=True, third_order=True, many_sorted=True)

D = {"alice", "bob"}
G = {"G(alice)": 0.25, "G(bob)": 0.75}


def every(g):
    """The degree to which every individual of ``D`` has the property."""
    return min(g(name) for name in D)


def some(g):
    return max(g(name) for name in D)


# ---------------------------------------------------------------------------
# The letter
# ---------------------------------------------------------------------------

def test_a_third_order_atom_is_a_letter_named_by_its_written_form():
    valuation = {"Pos(G)": 0.5, "Pos(λx. ¬G(x))": 0.25, "Ess(G, alice)": 0.75}
    assert evaluate(TO.parse("Pos(G)"), valuation) == 0.5
    assert evaluate(TO.parse("Pos(λx. ¬G(x))"), valuation) == 0.25
    assert evaluate(TO.parse("Ess(G, alice)"), valuation) == 0.75
    # 1/2 ⊗ 3/4 = 1/4, and 1/2 → 1/4 = 3/4
    assert evaluate(TO.parse("Pos(G) ⊗ Ess(G, alice)"), valuation) == 0.25
    assert evaluate(TO.parse("Pos(G) → Pos(λx. ¬G(x))"), valuation) == 0.75


def test_the_letter_takes_the_property_by_name():
    """``Pos(G)`` and ``Pos(H)`` are two letters, whatever ``G`` and ``H`` are."""
    valuation = {"Pos(G)": 1.0, "Pos(H)": 0.0, "G(alice)": 0.5, "H(alice)": 0.5}
    assert evaluate(TO.parse("Pos(G) → Pos(H)"), valuation) == 0.0
    with pytest.raises(KeyError, match=r"No degree for ground atom 'Pos\(H\)'"):
        evaluate(TO.parse("Pos(H)"), {"Pos(G)": 1.0})


def test_an_individual_inside_a_property_argument_is_grounded():
    valuation = {"Ess(λy. R(alice, y), alice)": 0.25, "Ess(λy. R(bob, y), bob)": 0.75}
    node = TO.parse("∀x Ess(λy. R(x, y), x)")
    assert evaluate(node, valuation, domain=D) == 0.25
    assert evaluate(TO.parse("∃x Ess(λy. R(x, y), x)"), valuation, domain=D) == 0.75
    assert (ground_quantifiers(node, domain=D).to_unicode_str()
            == "Ess(λy. R(alice, y), alice) ∧ Ess(λy. R(bob, y), bob)")


def test_the_deciders_read_the_letter():
    assert fuzzy_is_valid(TO.parse("Pos(G) → Pos(G)"))
    assert fuzzy_is_valid(TO.parse("(Pos(G) ⊗ (Pos(G) → Pos(H))) → Pos(H)"))
    # a letter of its own: nothing ties Pos(H) to Pos(G)
    assert not fuzzy_is_valid(TO.parse("Pos(G) → Pos(H)"))
    # nor Pos(λx. G(x)): another written form of the same property is another letter
    assert fuzzy_is_satisfiable(TO.parse("Pos(G) ⊗ ¬Pos(λx. G(x))"))
    model = fuzzy_get_model(TO.parse("Pos(G) ⊗ ¬Pos(H)"))
    assert model == {"Pos(G)": 1.0, "Pos(H)": 0.0, "degree": 1.0}


def test_a_valid_formula_stays_valid_whatever_the_third_order_predicate_is():
    """What the decider reports valid has degree 1 under every functional tried."""
    node = TO.parse("(Pos(G) ⊗ (Pos(G) → Pos(λx. ¬G(x)))) → Pos(λx. ¬G(x))")
    assert fuzzy_is_valid(node)
    for functional in (every, some, lambda g: g("alice"), lambda g: 0.5):
        assert evaluate(node, G, functionals={"Pos": functional}) == 1.0


def test_the_deciders_ground_the_individuals_of_a_third_order_atom():
    assert fuzzy_is_valid(TO.parse("∀x (Ess(G, x) → Ess(G, x))"), domain=D)
    assert fuzzy_is_valid(TO.parse("(∀x Ess(G, x)) → Ess(G, alice)"), domain=D)
    assert not fuzzy_is_valid(TO.parse("Ess(G, alice) → ∀x Ess(G, x)"), domain=D)


# ---------------------------------------------------------------------------
# A function of the caller
# ---------------------------------------------------------------------------

FUNCTIONAL = [
    # min(G(alice), G(bob))
    ("Pos(G)", {"Pos": every}, 0.25),
    ("Pos(G)", {"Pos": some}, 0.75),
    # the complement of G has the degrees 3/4 and 1/4
    ("Pos(λx. ¬G(x))", {"Pos": every}, 0.25),
    ("Pos(λx. ¬G(x))", {"Pos": some}, 0.75),
    # G(x) ⊕ ¬G(x) = 1 at every x
    ("Pos(λx. G(x) ⊕ ¬G(x))", {"Pos": every}, 1.0),
    # G(x) ⊗ ¬G(x) = 0 at every x
    ("Pos(λx. G(x) ⊗ ¬G(x))", {"Pos": some}, 0.0),
    # G(x) ∨ ¬G(x) = 3/4 at both
    ("Pos(λx. G(x) ∨ ¬G(x))", {"Pos": every}, 0.75),
    # an individual argument arrives as its name
    ("Ess(G, bob)", {"Ess": lambda g, name: g(name)}, 0.75),
    # 1/4 → 1/4 and 3/4 → 3/4
    ("∀x (Ess(G, x) ↔ G(x))", {"Ess": lambda g, name: g(name)}, 1.0),
    # Pos(G) → ¬Pos(λx. ¬G(x)) with "every": 1/4 → (1 − 1/4)
    ("Pos(G) → ¬Pos(λx. ¬G(x))", {"Pos": every}, 1.0),
    # with "some": 3/4 → (1 − 3/4) = 1/2
    ("Pos(G) → ¬Pos(λx. ¬G(x))", {"Pos": some}, 0.5),
    # two properties: the degree to which G is included in the complement of G
    ("Sub(G, λx. ¬G(x))", {"Sub": lambda g, h: min(min(1.0, 1.0 - g(n) + h(n)) for n in D)}, 0.5),
]


@pytest.mark.parametrize("text, functionals, expected", FUNCTIONAL)
def test_a_functional_computes_the_degree_from_the_property(text, functionals, expected):
    assert evaluate(TO.parse(text), G, domain=D, functionals=functionals) == expected


def test_a_lambda_term_with_a_variable_of_the_formula():
    """``∃x Ess(λy. R(x, y), x)``: for each ``x`` the property is ``R(x, ·)``."""
    valuation = {"R(alice, alice)": 0.125, "R(bob, bob)": 0.625,
                 "R(alice, bob)": 1.0, "R(bob, alice)": 0.0}
    functionals = {"Ess": lambda g, name: g(name)}
    assert evaluate(TO.parse("∃x Ess(λy. R(x, y), x)"), valuation, domain=D,
                    functionals=functionals) == 0.625
    assert evaluate(TO.parse("∀x Ess(λy. R(x, y), x)"), valuation, domain=D,
                    functionals=functionals) == 0.125


def test_a_functional_is_asked_in_place_of_the_valuation():
    assert evaluate(TO.parse("Pos(G)"), {**G, "Pos(G)": 1.0}, functionals={"Pos": every}) == 0.25
    # a predicate without an entry stays a letter
    assert evaluate(TO.parse("Pos(G) ∧ Neg(G)"), {**G, "Neg(G)": 0.125},
                    functionals={"Pos": every}) == 0.125


def test_the_result_of_a_functional_is_a_degree():
    assert evaluate(TO.parse("Pos(G)"), G, functionals={"Pos": lambda g: 7}) == 1.0
    assert evaluate(TO.parse("Pos(G)"), G, functionals={"Pos": lambda g: -1}) == 0.0


def test_a_property_reads_the_valuation_and_names_what_is_missing():
    with pytest.raises(KeyError, match=r"No degree for ground atom 'G\(bob\)'"):
        evaluate(TO.parse("Pos(G)"), {"G(alice)": 1.0}, functionals={"Pos": every})


def test_a_lambda_term_is_applied_to_as_many_names_as_it_binds():
    with pytest.raises(TypeError, match="binds 1 variable"):
        evaluate(TO.parse("Pos(λx. ¬G(x))"), G, functionals={"Pos": lambda g: g("alice", "bob")})


def test_sorted_individuals_in_a_third_order_atom():
    node = TO_SORTED.parse("∀x:S Ess(G, x)")
    assert evaluate(node, {"Ess(G, alice)": 0.5, "Ess(G, bob)": 0.25},
                    sort_universes={"S": D}) == 0.25
    assert evaluate(node, G, sort_universes={"S": D},
                    functionals={"Ess": lambda g, name: g(name)}) == 0.25
    # a sorted constant arrives as the constant it is
    assert evaluate(TO_SORTED.parse("Ess(G, bob:S)"), G,
                    functionals={"Ess": lambda g, name: g(name)}) == 0.75
