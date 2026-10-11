"""Fuzzy modal and fuzzy second-order reasoning over Z3 reals.

The degree of a fuzzy formula at a world of a finite fuzzy Kripke model is a
term of linear real arithmetic: the Łukasiewicz and the Gödel connectives are
piecewise linear, ``□`` and ``◇`` are a minimum and a maximum over the worlds,
and an individual quantifier is a minimum or maximum over the names of the
domain. This module builds that term once, for a model whose weights and degrees
are numbers or unknowns, and three things follow from it.

**A bounded search for a countermodel** (:func:`fuzzy_modal_search`). For
``n = 1 .. max_worlds`` every edge weight and every atom degree of a model with
``n`` worlds is an unknown real in ``[0, 1]``, and Z3 is asked for values that
give the formula a degree below 1 at world 0. A model that is found is a
countermodel, checked again by
:func:`~unicode_logic_kit.semantics.fuzzy_kripke.satisfies_fuzzy_modal`. When
there is none the result says exactly that: no countermodel with at most
``max_worlds`` worlds. It is NOT a proof of validity, and for the Gödel t-norm
it cannot become one by raising the bound: ``□¬¬P → ¬¬□P`` has degree 1 in
every finite model and a degree below 1 in an infinite one (worlds ``w_1, w_2,
…`` seen from ``w_0`` with weight 1, ``P`` of degree ``1/n`` at ``w_n``: every
``¬¬P`` is 1, so ``□¬¬P = 1``, while ``□P`` is the infimum 0 and ``¬¬□P = 0``).
The logic of ``□`` over ``[0, 1]``-valued Gödel Kripke models has no finite model
property (X. Caicedo and R. O. Rodríguez, "Standard Gödel modal logics", *Studia
Logica* 94(2), 2010, 189-214).

**The exact degree of a predicate quantifier**
(:func:`predicate_quantifier_degree`, :func:`second_order_degree`). ``∀P φ`` is
the infimum of ``φ`` over every FUZZY interpretation of ``P``, and ``∃P φ`` the
supremum. The body reads ``P`` at finitely many ground atoms (at each world it
reaches), so an interpretation is a point of a real cube and the quantifier is
an optimisation over it. The infimum is stated in the arithmetic itself, as the
greatest lower bound::

    d ≤ φ(p)  for every p in the cube,   and   e ≤ d  for every such bound e

which is a formula of quantified linear real arithmetic, a decidable theory. So
the degree is exact (a rational), also where the infimum is not reached (the
Gödel connectives jump) and where quantifiers alternate.

The interpretations are fuzzy, not crisp, and the choice matters: comprehension,
``∃P ∀x (P(x) ↔ Q(x))``, has degree 1 for every fuzzy ``Q`` because ``P`` may be
``Q`` itself, while over crisp sets ``P`` it has degree ``1/2`` at ``Q(a) = 1/2``
under Łukasiewicz.

**Validity and satisfiability with predicate quantifiers**, for the functions of
:mod:`~unicode_logic_kit.atp.z3_fuzzy` (:func:`second_order_degree_expr`).

Two limits hold on every route here.

- The t-norm is Łukasiewicz or Gödel. The product t-norm is not linear, and Z3
  does not decide nonlinear real arithmetic with quantifiers completely.
- An individual is named by a term, as in the evaluators: a quantifier ranges
  over the constant names of a domain, and two names are two individuals. A
  predicate quantifier can say that two terms differ (``∃P (P(a) ⊗ ¬P(b))``),
  so a route that DECIDES over all models refuses a formula whose bound
  predicates are applied to two different terms unless every one of them is a
  name of the declared domain (two such names are two individuals by the
  declaration). An evaluation of one given model is not affected.

A predicate in argument position (third order, ``Pos(G)``) is part of the written
form of its atom: the atom is a letter of its own. A predicate quantifier that
binds such a predicate is refused by name.
"""

import itertools
from dataclasses import dataclass
from fractions import Fraction
from typing import (
    Any, Callable, Collection, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple,
)

from z3 import (
    And as Z3And, ArithRef, BoolRef, ForAll, Implies as Z3Implies, Or as Z3Or,
    Real, RealVal, Solver, sat, unsat,
)

from ..fol._atom_keys import AtomKeys, find_key
from ..fol._free_parameters import free_parameter_names
from ..fol._msfl_nodes import key_text
from ..fol._truth_constants import truth_value as _truth_value
from ..fol.frames import resolve_frame
from ..fol.nodes import (
    Node, Atom, Constant, SortedConstant, Lambda, PredicateTerm,
    Quantifier, SortedQuantifier, SecondOrderQuantifier,
    Box, Diamond, Knows, Believes, Says, Wants,
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction, LukImplication, LukEquivalence,
    substitute,
)
from ..semantics.fuzzy import _reject_comparison_atom, check_sorted_constants
from ..semantics.fuzzy_kripke import (
    FuzzyKripkeModel, quantifier_universe, refuse_node, relation_name,
    satisfies_fuzzy_modal,
)
from ..semantics.tnorm import GODEL, LUKASIEWICZ, TNorm
from .z3_fuzzy import _rng_value, _z3_max, _z3_min, _z3_tnorm_ops

__all__ = [
    "FuzzyModalSearchResult", "fuzzy_modal_search", "fuzzy_modal_countermodel",
    "fuzzy_kripke_model_to_dict", "fuzzy_kripke_model_from_dict",
    "predicate_quantifier_degree", "second_order_degree", "second_order_degree_expr",
]

_BINARY = (WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
           LukImplication, LukEquivalence)
_MODAL = (Box, Diamond, Knows, Believes, Says, Wants)

#: The frame conditions a search can ask for, each in its graded form (see
#: :func:`fuzzy_modal_search`).
_FRAME_CONDITIONS = ("refl", "sym", "trans", "serial", "eucl")

#: The time Z3 is given for the degree of one predicate quantifier of an evaluation, in
#: milliseconds.
PREDICATE_QUANTIFIER_TIMEOUT = 60000


def _linear_tnorm(tnorm: TNorm, caller: str) -> str:
    """The name of ``tnorm`` if it is one this module computes with, else a refusal."""
    if tnorm is LUKASIEWICZ or tnorm is GODEL:
        return tnorm.name
    raise NotImplementedError(
        f"{caller}: a predicate quantifier is an infimum or supremum over every fuzzy "
        f"interpretation of its predicate, computed here as linear real arithmetic. The "
        f"t-norm {tnorm.name!r} of this model is not tnorm.LUKASIEWICZ or tnorm.GODEL, "
        "the two whose connectives are piecewise linear.")


# =========================
# What the encoder reads of a model
# =========================

class _Letters:
    """One valuation and no worlds: the reading of a formula without modal operators."""

    def __init__(self, degree_of: Callable[[Atom, str], ArithRef], caller: str):
        self._degree_of = degree_of
        self._caller = caller

    def place(self, world: Any) -> str:
        """The part of a bound atom's name that tells its world: none, there is one."""
        return ""

    def targets(self, relation: str, world: Any) -> Sequence[Any]:
        """Refuse: a modal operator has no reading without a model."""
        raise TypeError(
            f"{self._caller}: a modal operator is read at a world of a fuzzy Kripke model, "
            "and this route has one valuation and no worlds. Evaluate the formula with "
            "semantics.fuzzy_kripke.satisfies_fuzzy_modal, or search for a countermodel "
            "with atp.z3_fuzzy_kripke.fuzzy_modal_search.")

    def weight(self, relation: str, world: Any, target: Any) -> ArithRef:
        """Never reached: :meth:`targets` refuses first."""
        raise AssertionError("a valuation has no edges")

    def degree(self, world: Any, atom: Atom, key: str) -> ArithRef:
        """The degree of a free atom."""
        return self._degree_of(atom, key)


class _Given:
    """A :class:`FuzzyKripkeModel`: every weight and every degree is a number."""

    def __init__(self, model: FuzzyKripkeModel):
        self._model = model
        self._places: Dict[Any, int] = {}

    def place(self, world: Any) -> str:
        """A name for ``world`` that no other world of this reading has."""
        return str(self._places.setdefault(world, len(self._places)))

    def targets(self, relation: str, world: Any) -> Sequence[Any]:
        """The worlds ``world`` sees with a positive weight.

        A world seen with weight 0 contributes the neutral element of the aggregate
        (``0 → y = 1`` for ``□``, ``0 ⊗ y = 0`` for ``◇``, under both t-norms), so leaving
        it out gives the degree :func:`satisfies_fuzzy_modal` computes over all of them.
        """
        edges = self._model.relations.get(relation, {})
        seen = {target for (source, target), weight in edges.items()
                if source == world and weight > 0}
        return sorted(seen, key=repr)

    def weight(self, relation: str, world: Any, target: Any) -> ArithRef:
        """The weight of an edge, exactly."""
        return RealVal(Fraction(self._model.relation_weight(relation, world, target)))

    def degree(self, world: Any, atom: Atom, key: str) -> ArithRef:
        """The degree of a free atom at ``world``, exactly (0 where the model has none)."""
        degrees = self._model.valuation.get(world, {})
        found = find_key(degrees, atom)
        return RealVal(0 if found is None else Fraction(degrees[found]))


class _Unknown:
    """A model with ``size`` worlds whose weights and degrees are unknown reals."""

    def __init__(self, size: int):
        self.worlds: Tuple[int, ...] = tuple(range(size))
        self.weights: Dict[Tuple[str, int, int], ArithRef] = {}
        self.degrees: Dict[Tuple[int, str], ArithRef] = {}

    def place(self, world: Any) -> str:
        """The world's number."""
        return str(world)

    def targets(self, relation: str, world: Any) -> Sequence[Any]:
        """Every world: an edge of weight 0 is an edge that is not there."""
        return self.worlds

    def weight(self, relation: str, world: Any, target: Any) -> ArithRef:
        """The unknown weight of an edge."""
        found = self.weights.get((relation, world, target))
        if found is None:
            found = Real(f"fuzzy!edge!{relation}!{world}!{target}")
            self.weights[(relation, world, target)] = found
        return found

    def degree(self, world: Any, atom: Atom, key: str) -> ArithRef:
        """The unknown degree of a free atom at ``world``."""
        found = self.degrees.get((world, key))
        if found is None:
            found = Real(f"fuzzy!atom!{world}!{key}")
            self.degrees[(world, key)] = found
        return found


# =========================
# The encoder
# =========================

class _Binder:
    """One predicate quantifier under encoding, and the reals of its bound atoms.

    A bound predicate has a degree of its own at each world for each ground atom the
    body reads there. ``reals`` holds one unknown for each such pair, made when the body
    first reads it.
    """

    def __init__(self, node: SecondOrderQuantifier, token: int):
        self.predicate = node.predicate
        self.arity = node.arity
        self.token = token
        self.reals: Dict[Tuple[Any, str], ArithRef] = {}

    def real(self, place: str, world: Any, key: str) -> ArithRef:
        """The unknown that stands for the bound atom ``key`` at ``world``."""
        found = self.reals.get((world, key))
        if found is None:
            found = Real(f"fuzzy!bound!{self.token}!{place}!{key}")
            self.reals[(world, key)] = found
        return found


@dataclass(frozen=True, eq=False)
class _Definition:
    """A real that is the degree of a predicate quantifier, and the constraint saying so."""

    value: ArithRef
    constraint: BoolRef


def _merge(*groups: Tuple[_Definition, ...]) -> Tuple[_Definition, ...]:
    """The definitions of several subterms, each once, in the order they are met."""
    merged: List[_Definition] = []
    for group in groups:
        for definition in group:
            if not any(definition is kept for kept in merged):
                merged.append(definition)
    return tuple(merged)


def _is_universal(quantifier: str, caller: str) -> bool:
    """Whether a quantifier glyph is the universal one; any other than the two is refused."""
    if quantifier in ("∀", "forall"):
        return True
    if quantifier in ("∃", "exists"):
        return False
    raise ValueError(f"{caller}: unknown quantifier type {quantifier!r}")


class _Encoder:
    """Degree terms of fuzzy formulas over one reading of a model.

    ``reading`` is a :class:`_Letters`, a :class:`_Given` or an :class:`_Unknown`.
    ``term`` builds the degree of a formula at a world and, next to it, the
    definitions of the predicate quantifiers the term depends on. After the encoding,
    ``bound_terms`` holds every argument term a bound predicate was applied to.
    """

    def __init__(self, reading: Any, tnorm: str, caller: str,
                 domain: Optional[Collection[str]] = None,
                 sort_universes: Optional[Mapping[str, Collection[str]]] = None,
                 keys: Optional[AtomKeys] = None):
        self.reading = reading
        self.ops = _z3_tnorm_ops(tnorm)
        self.caller = caller
        self.domain = None if domain is None else frozenset(domain)
        self.sort_universes = sort_universes
        self.keys = keys if keys is not None else AtomKeys(caller)
        self.bound_terms: Dict[str, Node] = {}
        self._tokens = itertools.count()
        self._memo: Dict[Tuple[Node, Any, Tuple[_Binder, ...]],
                         Tuple[ArithRef, Tuple[_Definition, ...]]] = {}

    # --- entry ---

    def degree(self, formula: Node, world: Any) -> Tuple[ArithRef, List[BoolRef]]:
        """The degree of ``formula`` at ``world`` and the constraints it holds under."""
        expr, definitions = self.term(formula, world, ())
        return expr, [definition.constraint for definition in definitions]

    def open_degree(self, formula: Node, world: Any) -> Tuple[ArithRef, List[BoolRef]]:
        """A term that is below 1 for some values exactly when the degree of ``formula`` is.

        A universal predicate quantifier at the root of the formula (below other universal
        quantifiers and weak conjunctions, which are minima) is an infimum, and an infimum
        is below 1 exactly when one of its values is. So such a quantifier is left open:
        its bound atoms become unknowns of the caller's problem, each in the unit
        interval, instead of a definition with quantifiers of its own. The term is NOT the
        degree of the formula; it serves a route that asks whether the degree can be
        below 1 (a countermodel, a validity check).
        """
        opened: List[_Binder] = []
        expr, definitions = self._open(formula, world, (), opened)
        constraints = [definition.constraint for definition in definitions]
        for binder in opened:
            for real in binder.reals.values():
                constraints += [real >= 0, real <= 1]
        return expr, constraints

    def _open(self, node: Node, world: Any, env: Tuple[_Binder, ...],
              opened: List[_Binder]) -> Tuple[ArithRef, Tuple[_Definition, ...]]:
        if isinstance(node, SecondOrderQuantifier) and _is_universal(node.type, self.caller):
            binder = _Binder(node, next(self._tokens))
            opened.append(binder)
            return self._open(node.formula, world, env + (binder,), opened)
        if (isinstance(node, (Quantifier, SortedQuantifier))
                and _is_universal(node.type, self.caller)):
            names = quantifier_universe(node, self.domain, self.sort_universes, self.caller)
            parts = [self._open(substitute(node.formula, node.variable, Constant(name)),
                                world, env, opened) for name in names]
        elif isinstance(node, WeakConjunction):
            parts = [self._open(node.left, world, env, opened),
                     self._open(node.right, world, env, opened)]
        else:
            return self.term(node, world, env)
        result = parts[0][0]
        for degree, _ in parts[1:]:
            result = _z3_min(result, degree)
        return result, _merge(*[definitions for _, definitions in parts])

    def term(self, node: Node, world: Any, env: Tuple[_Binder, ...]
             ) -> Tuple[ArithRef, Tuple[_Definition, ...]]:
        """The degree of ``node`` at ``world`` under the binders ``env``, encoded once."""
        memo_key = (node, world, env)
        found = self._memo.get(memo_key)
        if found is None:
            found = self._memo[memo_key] = self._encode(node, world, env)
        return found

    # --- cases ---

    def _encode(self, node: Node, world: Any, env: Tuple[_Binder, ...]
                ) -> Tuple[ArithRef, Tuple[_Definition, ...]]:
        if isinstance(node, Atom):
            return self._atom(node, world, env), ()
        if isinstance(node, LukNegation):
            inner, definitions = self.term(node.formula, world, env)
            return self.ops["neg"](inner), definitions
        if isinstance(node, _BINARY):
            left, left_definitions = self.term(node.left, world, env)
            right, right_definitions = self.term(node.right, world, env)
            return (self._connective(node, left, right),
                    _merge(left_definitions, right_definitions))
        if isinstance(node, (Quantifier, SortedQuantifier)):
            return self._individuals(node, world, env)
        if isinstance(node, _MODAL):
            return self._modality(node, world, env)
        if isinstance(node, SecondOrderQuantifier):
            return self._predicates(node, world, env)
        refuse_node(node, self.caller)

    def _connective(self, node: Node, left: ArithRef, right: ArithRef) -> ArithRef:
        if isinstance(node, WeakConjunction):
            return _z3_min(left, right)
        if isinstance(node, WeakDisjunction):
            return _z3_max(left, right)
        if isinstance(node, StrongConjunction):
            return self.ops["sconj"](left, right)
        if isinstance(node, StrongDisjunction):
            return self.ops["sdisj"](left, right)
        if isinstance(node, LukImplication):
            return self.ops["impl"](left, right)
        # LukEquivalence: min(a → b, b → a), for every t-norm
        return _z3_min(self.ops["impl"](left, right), self.ops["impl"](right, left))

    def _atom(self, node: Atom, world: Any, env: Tuple[_Binder, ...]) -> ArithRef:
        constant = _truth_value(node)
        if constant is not None:
            return RealVal(1 if constant else 0)
        _reject_comparison_atom(node, self.caller)
        self._refuse_bound_argument(node, env)
        key = self.keys.key(node)
        binder = next((b for b in reversed(env) if b.predicate == node.predicate), None)
        if binder is None:
            return self.reading.degree(world, node, key)
        if len(node.args) != binder.arity:
            raise ValueError(
                f"{self.caller}: a predicate quantifier binds {binder.predicate} at arity "
                f"{binder.arity}, and its body applies {binder.predicate} to "
                f"{len(node.args)} argument(s) in {node.to_unicode_str()!r}. A bound "
                "predicate has one arity.")
        for argument in node.args:
            self.bound_terms.setdefault(key_text(argument), argument)
        return binder.real(self.reading.place(world), world, key)

    def _refuse_bound_argument(self, node: Atom, env: Tuple[_Binder, ...]) -> None:
        """Refuse an atom that has a bound predicate inside one of its arguments."""
        if not env:
            return
        bound = {binder.predicate for binder in env}
        for argument in node.args:
            if not isinstance(argument, (PredicateTerm, Lambda)):
                continue
            for part in argument.walk():
                name = (part.name if isinstance(part, PredicateTerm)
                        else part.predicate if isinstance(part, Atom) else None)
                if name in bound:
                    raise NotImplementedError(
                        f"{self.caller}: the predicate {name} is bound by a predicate "
                        f"quantifier and stands in argument position in "
                        f"{node.to_unicode_str()!r} (third order). A predicate quantifier "
                        "ranges over the degrees of the ground atoms of its predicate, and "
                        "an atom that takes the predicate itself as an argument is none of "
                        "them, so the quantifier would not reach it.")

    def _individuals(self, node: Any, world: Any, env: Tuple[_Binder, ...]
                     ) -> Tuple[ArithRef, Tuple[_Definition, ...]]:
        universal = _is_universal(node.type, self.caller)
        names = quantifier_universe(node, self.domain, self.sort_universes, self.caller)
        result: Optional[ArithRef] = None
        definitions: Tuple[_Definition, ...] = ()
        for name in names:
            instance = substitute(node.formula, node.variable, Constant(name))
            degree, inner = self.term(instance, world, env)
            definitions = _merge(definitions, inner)
            if result is None:
                result = degree
            else:
                result = _z3_min(result, degree) if universal else _z3_max(result, degree)
        assert result is not None       # quantifier_universe refuses an empty universe
        return result, definitions

    def _modality(self, node: Any, world: Any, env: Tuple[_Binder, ...]
                  ) -> Tuple[ArithRef, Tuple[_Definition, ...]]:
        relation = relation_name(node)
        assert relation is not None
        possibility = isinstance(node, Diamond)
        result: Optional[ArithRef] = None
        definitions: Tuple[_Definition, ...] = ()
        for target in self.reading.targets(relation, world):
            weight = self.reading.weight(relation, world, target)
            degree, inner = self.term(node.formula, target, env)
            definitions = _merge(definitions, inner)
            if possibility:
                part = self.ops["sconj"](weight, degree)
                result = part if result is None else _z3_max(result, part)
            else:
                part = self.ops["impl"](weight, degree)
                result = part if result is None else _z3_min(result, part)
        if result is None:              # no world is seen: sup ∅ = 0, inf ∅ = 1
            return RealVal(0 if possibility else 1), ()
        return result, definitions

    def _predicates(self, node: SecondOrderQuantifier, world: Any, env: Tuple[_Binder, ...]
                    ) -> Tuple[ArithRef, Tuple[_Definition, ...]]:
        """The infimum (``∀P``) or supremum (``∃P``) of the body over the bound atoms.

        With ``p`` the reals of the bound atoms and ``φ(p)`` the degree of the body, the
        degree ``d`` of ``∀P φ`` is the greatest lower bound of ``φ`` over the unit cube::

            ∀p (p in the cube → d ≤ φ(p))   ∧   ∀e (∀p (p in the cube → e ≤ φ(p)) → e ≤ d)

        and dually for ``∃P``. A predicate quantifier inside the body has a degree that
        depends on ``p``; its real is bound together with ``p``, under its own definition.
        """
        universal = _is_universal(node.type, self.caller)
        binder = _Binder(node, next(self._tokens))
        body, inner = self.term(node.formula, world, env + (binder,))
        reals = list(binder.reals.values())
        if not reals:
            # The body never reads the bound predicate: every interpretation gives it
            # the one degree it has.
            return body, inner
        bound = reals + [definition.value for definition in inner]
        cube = Z3And(*[side for real in reals for side in (real >= 0, real <= 1)],
                     *[definition.constraint for definition in inner])

        def is_bound(candidate: ArithRef) -> BoolRef:
            """``candidate`` bounds the body from below (``∀P``) or above (``∃P``)."""
            side = candidate <= body if universal else body <= candidate
            return ForAll(bound, Z3Implies(cube, side))

        value = Real(f"fuzzy!{'inf' if universal else 'sup'}!{binder.token}")
        other = Real(f"fuzzy!other!{binder.token}")
        closest = ForAll([other], Z3Implies(
            is_bound(other), other <= value if universal else value <= other))
        return value, (_Definition(value, Z3And(is_bound(value), closest)),)

    # --- the reading of terms as individuals ---

    def refuse_coreference(self, names: Iterable[str]) -> None:
        """Refuse a formula whose bound predicates tell apart terms that may be one individual.

        ``names`` are the constant names the caller declared as the individuals (the
        domain and the universes of the sorts): two of them are two individuals. Any
        other term (a constant outside them, a function term, a free variable) may name
        an individual that another term names too, and a route that reads a term as its
        own individual would then decide another formula.

        Raises:
            NotImplementedError: the bound predicates of the encoded formula are applied
                to two different terms, and one of them is not a declared name.
        """
        if len(self.bound_terms) < 2:
            return
        declared = frozenset(names)
        loose = sorted(text for text, term in self.bound_terms.items()
                       if not (isinstance(term, (Constant, SortedConstant))
                               and term.name in declared))
        if not loose:
            return
        other = next(text for text in sorted(self.bound_terms) if text != loose[0])
        raise NotImplementedError(
            f"{self.caller}: predicate quantifiers of the formula apply their bound "
            f"predicates to the different terms {loose[0]} and {other}, and {loose[0]} is "
            "not a name of the declared domain. Two terms may name one individual, and a "
            "predicate quantifier can say that they do not; this route names an individual "
            "by its term, so it would decide the formula for the models in which they "
            "differ and report that for all. Declare both as names of the domain (two "
            "names of the domain are two individuals), or evaluate the formula in one "
            "given model.")


# =========================
# The degree of a predicate quantifier in a given model
# =========================

def _solver(constraints: Sequence[BoolRef], timeout: int) -> Solver:
    """A solver holding ``constraints``, to be asked ONE question.

    One question, and a solver of its own for the next: a solver that is asked again
    after ``push`` / ``pop`` works incrementally, and Z3 then no longer decides the
    quantified constraints a predicate quantifier is defined by (it answers ``unknown``
    where the same constraints, asked once, are decided at once).
    """
    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(*constraints)
    return solver


def _solve_for(expr: ArithRef, constraints: Sequence[BoolRef], caller: str,
               timeout: int) -> Fraction:
    """The one value ``expr`` has under ``constraints``, which determine it."""
    solver = _solver(constraints, timeout)
    result = Real("fuzzy!result")
    solver.add(result == expr)
    outcome = solver.check()
    if outcome != sat:
        raise RuntimeError(
            f"{caller}: Z3 did not determine the degree of a predicate quantifier "
            f"({outcome}) within {timeout} ms. The degree is an optimum over one real per "
            "bound atom and world; a smaller model or domain has fewer of them.")
    return _rng_value(solver.model(), result)


def predicate_quantifier_degree(formula: Node, model: FuzzyKripkeModel, world: Any) -> Fraction:
    """The exact degree of ``formula`` at ``world`` of ``model``, as a rational.

    Meant for a formula with a predicate quantifier, which
    :func:`~unicode_logic_kit.semantics.fuzzy_kripke.satisfies_fuzzy_modal` hands over
    here; it computes any formula of that evaluator's scope. The weights and degrees of
    the model are read exactly (a float is the rational it stores), so the result is the
    degree of that model and not of one near it.

    Raises:
        NotImplementedError: the model's t-norm is not ``tnorm.LUKASIEWICZ`` or
            ``tnorm.GODEL``; a bound predicate stands in argument position; a node
            outside the scope of the graded Kripke semantics.
        ValueError: a quantifier without its universe; a bound predicate applied at
            another arity than its quantifier states.
        RuntimeError: Z3 did not determine the degree within
            :data:`PREDICATE_QUANTIFIER_TIMEOUT`.
    """
    caller = "satisfies_fuzzy_modal"
    encoder = _Encoder(_Given(model), _linear_tnorm(model.tnorm, caller), caller,
                       model.domain, model.sort_universes)
    expr, constraints = encoder.degree(formula, world)
    return _solve_for(expr, constraints, caller, PREDICATE_QUANTIFIER_TIMEOUT)


def second_order_degree(formula: Node, degree_of: Callable[[Atom], float], tnorm: str,
                        domain: Optional[Collection[str]] = None,
                        sort_universes: Optional[Mapping[str, Collection[str]]] = None,
                        keys: Optional[AtomKeys] = None,
                        caller: str = "evaluate") -> Fraction:
    """The exact degree of a formula without modal operators under one valuation.

    ``degree_of`` gives the degree of a free ground atom (the caller's valuation); the
    atoms of a bound predicate are the unknowns its quantifier ranges over. This is what
    :func:`~unicode_logic_kit.semantics.fuzzy.evaluate` computes a predicate quantifier
    with.

    Raises:
        NotImplementedError: ``tnorm`` is ``"product"``; a bound predicate stands in
            argument position.
        TypeError: a modal operator, a comparison atom, or a classical connective.
        ValueError: an unknown t-norm; a quantifier without its universe.
        RuntimeError: Z3 did not determine the degree within
            :data:`PREDICATE_QUANTIFIER_TIMEOUT`.
    """
    if tnorm == "product":
        raise NotImplementedError(
            f"{caller}: a predicate quantifier is an infimum or supremum over every fuzzy "
            "interpretation of its predicate, computed as linear real arithmetic; the "
            "product t-norm is not linear. Use tnorm='lukasiewicz' or tnorm='godel'.")
    reading = _Letters(lambda atom, key: RealVal(Fraction(degree_of(atom))), caller)
    encoder = _Encoder(reading, tnorm, caller, domain, sort_universes, keys)
    expr, constraints = encoder.degree(formula, None)
    return _solve_for(expr, constraints, caller, PREDICATE_QUANTIFIER_TIMEOUT)


def second_order_degree_expr(formula: Node, tnorm: str,
                             domain: Optional[Collection[str]] = None,
                             sort_universes: Optional[Mapping[str, Collection[str]]] = None,
                             below_one: bool = False,
                             ) -> Tuple[ArithRef, List[BoolRef], Dict[str, ArithRef]]:
    """The degree of a formula with predicate quantifiers, every free atom an unknown.

    The triple :func:`~unicode_logic_kit.atp.z3_fuzzy.degree_expr` returns: the degree, the
    constraints it holds under (the unit interval of every free atom, and the definition of
    every predicate quantifier), and the unknown of every free atom by its key.

    With ``below_one=True`` the first component is not the degree but a term that can be
    below 1 exactly when the degree can (:meth:`_Encoder.open_degree`): what a validity
    check asks, without the quantifiers a universal predicate quantifier at the root of
    the formula would cost.

    Raises:
        NotImplementedError: a free variable in a formula with an individual quantifier;
            bound predicates applied to two different terms that are not both names of
            ``domain`` / ``sort_universes`` (see the module docstring); a bound predicate
            in argument position; the product t-norm.
        TypeError: a modal operator, a comparison atom, or a classical connective.
        ValueError: an unknown t-norm; a quantifier without its universe; a sorted
            constant its universe does not hold.
    """
    caller = "z3_fuzzy"
    _refuse_parameters(formula, caller)
    check_sorted_constants(formula, sort_universes, caller)
    atom_vars: Dict[str, ArithRef] = {}

    def unknown(atom: Atom, key: str) -> ArithRef:
        found = atom_vars.get(key)
        if found is None:
            found = atom_vars[key] = Real(f"fuzzy!{key}")
        return found

    encoder = _Encoder(_Letters(unknown, caller), tnorm, caller, domain, sort_universes)
    expr, constraints = (encoder.open_degree(formula, None) if below_one
                         else encoder.degree(formula, None))
    encoder.refuse_coreference(_declared_names(domain, sort_universes))
    for real in atom_vars.values():
        constraints.append(real >= RealVal(0))
        constraints.append(real <= RealVal(1))
    return expr, constraints, atom_vars


def _refuse_parameters(formula: Node, caller: str) -> None:
    """Refuse a free variable in a formula that has an individual quantifier.

    The refusal of :func:`~unicode_logic_kit.atp.z3_fuzzy.degree_expr`, for the same
    reason: a free variable is one unknown element of the domain, and a route that grounds
    the quantifiers has no reading of it.
    """
    if not (formula.count(Quantifier) or formula.count(SortedQuantifier)):
        return
    parameters = free_parameter_names([formula])
    if parameters:
        raise NotImplementedError(
            f"{caller}: the variable(s) {list(parameters)} are free in a quantified "
            "formula. A free variable is a parameter, one unknown element of the domain, "
            "and deciding it would take the formula under every assignment of the "
            "domain's elements to it; this decider has no such reading and would "
            "answer about another formula. Bind the variable with a quantifier, or "
            "write a constant of the domain in its place.")


def _declared_names(domain: Optional[Collection[str]],
                    sort_universes: Optional[Mapping[str, Collection[str]]]) -> frozenset:
    """Every constant name the caller declared as an individual."""
    names = set(domain or ())
    for universe in (sort_universes or {}).values():
        names |= set(universe)
    return frozenset(names)


# =========================
# The bounded search for a countermodel
# =========================

@dataclass(frozen=True)
class FuzzyModalSearchResult:
    """The outcome of one :func:`fuzzy_modal_search` call.

    ``model``
        a :class:`~unicode_logic_kit.semantics.fuzzy_kripke.FuzzyKripkeModel` in which the
        formula has a degree below 1 at world 0, or ``None``.
    ``degree``
        the degree of the formula at world 0 of ``model``, as
        :func:`~unicode_logic_kit.semantics.fuzzy_kripke.satisfies_fuzzy_modal` computes it
        (below 1); ``None`` without a model.
    ``exhausted``
        ``True`` iff there is no model because every size up to ``max_worlds`` was
        decided and none has a countermodel: no countermodel with at most ``max_worlds``
        worlds. Never a proof of validity (see the module docstring).
    ``worlds``
        the largest number of worlds that was decided.
    ``unsupported``
        ``None``, or the ``"ExceptionType: message"`` with which the formula was refused.
    ``detail``
        a sentence saying which of these happened.
    ``timed_out``
        ``True`` iff Z3 did not decide a size within the time limit.
    """

    model: Optional[FuzzyKripkeModel]
    degree: Optional[float]
    exhausted: bool
    worlds: int
    unsupported: Optional[str] = None
    detail: str = ""
    timed_out: bool = False

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict (the model, if any, by :func:`fuzzy_kripke_model_to_dict`)."""
        return {
            "found": self.model is not None,
            "degree": self.degree,
            "exhausted": self.exhausted,
            "worlds": self.worlds,
            "unsupported": self.unsupported,
            "detail": self.detail,
            "timed_out": self.timed_out,
            "model": None if self.model is None else fuzzy_kripke_model_to_dict(self.model),
        }


def fuzzy_kripke_model_to_dict(model: FuzzyKripkeModel) -> dict:
    """Render a :class:`FuzzyKripkeModel` as a JSON-compatible dict.

    ``{"worlds": [...], "relations": {name: [[w, w', weight], ...]}, "valuation":
    {str(world): {atom_key: degree}}, "tnorm": name}``, with ``"domain"`` and
    ``"sort_universes"`` only when the model has them. An edge of weight 0 and an atom of
    degree 0 are left out: a model reads what is absent as 0.
    """
    data: dict = {
        "worlds": sorted(model.worlds, key=repr),
        "relations": {
            name: sorted(([source, target, weight] for (source, target), weight
                          in edges.items() if weight > 0), key=repr)
            for name, edges in sorted(model.relations.items())
        },
        "valuation": {
            str(world): {key: degree for key, degree in sorted(degrees.items()) if degree > 0}
            for world, degrees in sorted(model.valuation.items(), key=lambda item: repr(item[0]))
        },
        "tnorm": model.tnorm.name,
    }
    if model.domain is not None:
        data["domain"] = sorted(model.domain)
    if model.sort_universes is not None:
        data["sort_universes"] = {sort: sorted(names)
                                  for sort, names in sorted(model.sort_universes.items())}
    return data


def fuzzy_kripke_model_from_dict(data: dict) -> FuzzyKripkeModel:
    """Rebuild a :class:`FuzzyKripkeModel` from :func:`fuzzy_kripke_model_to_dict` output.

    The key of a world in ``"valuation"`` is ``str(world)`` and is resolved against the
    ``"worlds"`` list.

    Raises:
        ValueError: ``"tnorm"`` names none of the built-in t-norms.
    """
    from ..semantics.tnorm import get_tnorm
    worlds = list(data["worlds"])
    by_text = {str(world): world for world in worlds}
    relations = {name: {(source, target): weight for source, target, weight in edges}
                 for name, edges in data.get("relations", {}).items()}
    valuation = {by_text.get(key, key): dict(degrees)
                 for key, degrees in data.get("valuation", {}).items()}
    return FuzzyKripkeModel(worlds, relations, valuation,
                            tnorm=get_tnorm(data.get("tnorm", "lukasiewicz")),
                            domain=data.get("domain"),
                            sort_universes=data.get("sort_universes"))


def _conditions(relation: str, frame: str, systems: Optional[Mapping[str, str]],
                caller: str) -> Tuple[str, ...]:
    """The frame conditions of one relation, each one this module has a graded form of."""
    systems = systems or {}
    if relation == "alethic":
        name = frame
    elif relation.startswith("K:"):
        name = systems.get("epistemic", "K")
    elif relation.startswith("B:"):
        name = systems.get("doxastic", "K")
    else:
        name = "K"          # Says / Wants: no frame condition, as in the crisp routes
    try:
        conditions = resolve_frame(name)
    except ValueError as exc:
        raise ValueError(f"{caller}: {exc}") from None
    for condition in conditions:
        if condition not in _FRAME_CONDITIONS:
            raise NotImplementedError(
                f"{caller}: the frame {name!r} has the condition {condition!r}, and this "
                f"search has a graded form of {', '.join(_FRAME_CONDITIONS)} only.")
    return conditions


def _frame_constraints(reading: _Unknown, relation: str, conditions: Sequence[str],
                       ops: dict) -> List[BoolRef]:
    """The graded form of each frame condition, over every edge of ``relation``."""
    worlds = reading.worlds

    def weight(source: int, target: int) -> ArithRef:
        return reading.weight(relation, source, target)

    constraints: List[BoolRef] = []
    for condition in conditions:
        if condition == "refl":
            constraints += [weight(w, w) == 1 for w in worlds]
        elif condition == "sym":
            constraints += [weight(w, v) == weight(v, w)
                            for w in worlds for v in worlds if w < v]
        elif condition == "trans":
            constraints += [ops["sconj"](weight(w, v), weight(v, u)) <= weight(w, u)
                            for w in worlds for v in worlds for u in worlds]
        elif condition == "serial":
            constraints += [Z3Or(*[weight(w, v) == 1 for v in worlds]) for w in worlds]
        elif condition == "eucl":
            constraints += [ops["sconj"](weight(w, v), weight(w, u)) <= weight(v, u)
                            for w in worlds for v in worlds for u in worlds]
    return constraints


def _relations_of(formula: Node) -> Tuple[str, ...]:
    """The relation names the modal operators of ``formula`` are read over, sorted."""
    names = set()
    for node in formula.walk():
        name = relation_name(node)
        if name is not None:
            names.add(name)
    return tuple(sorted(names))


def fuzzy_modal_search(formula: Node, *, tnorm: str = "lukasiewicz", frame: str = "K",
                       systems: Optional[Mapping[str, str]] = None,
                       max_worlds: int = 3, crisp_frame: bool = False,
                       domain: Optional[Iterable[str]] = None,
                       sort_universes: Optional[Mapping[str, Iterable[str]]] = None,
                       timeout: int = 10000) -> FuzzyModalSearchResult:
    """Search the fuzzy Kripke models with at most ``max_worlds`` worlds for a countermodel.

    A countermodel is a model in which ``formula`` has a degree below 1 at world 0. For
    each size ``n = 1 .. max_worlds`` the edge weights and atom degrees of a model with
    the worlds ``0 .. n-1`` are unknown reals in ``[0, 1]``, and Z3 decides whether some
    choice gives the formula a degree below 1; the first model found is returned, after
    :func:`~unicode_logic_kit.semantics.fuzzy_kripke.satisfies_fuzzy_modal` has computed
    its degree again. A size without a countermodel is decided exactly, so
    ``exhausted=True`` means: no countermodel with at most ``max_worlds`` worlds. It is
    not a proof of validity (see the module docstring).

    Args:
        formula: a formula of the scope of
            :func:`~unicode_logic_kit.semantics.fuzzy_kripke.satisfies_fuzzy_modal`.
        tnorm: ``"lukasiewicz"`` (default) or ``"godel"``.
        frame: the frame of ``□`` / ``◇``, a name of
            :data:`unicode_logic_kit.fol.frames.FRAMES` whose conditions are among
            reflexive, symmetric, transitive, serial and euclidean (``"K"``, ``"T"``,
            ``"B"``, ``"K4"``, ``"S4"``, ``"S5"``, ``"KD"``, ``"KD45"`` …). Each is read
            in its graded form, with ``⊗`` the t-norm: ``R(w, w) = 1``; ``R(w, v) =
            R(v, w)``; ``R(w, v) ⊗ R(v, u) ≤ R(w, u)``; some ``v`` with ``R(w, v) = 1``;
            ``R(w, v) ⊗ R(w, u) ≤ R(v, u)``. Under these the axioms T, B, 4, D and 5 have
            degree 1.
        systems: the frame of the relations of ``K_a`` (``{"epistemic": "S5"}``) and of
            ``B_a`` (``{"doxastic": "KD45"}``); ``"K"`` by default, as for ``Says`` and
            ``Wants`` always.
        max_worlds: the largest number of worlds searched.
        crisp_frame: if true, every edge weight is 0 or 1 (a crisp frame under a fuzzy
            valuation).
        domain: the constant names ``∀x`` / ``∃x`` range over, at every world.
        sort_universes: the constant names ``∀x:S`` / ``∃x:S`` range over.
        timeout: the time Z3 is given for each size, in milliseconds.

    Returns:
        A :class:`FuzzyModalSearchResult`. A formula outside the scope is reported in
        ``unsupported`` with the message of its refusal.

    Raises:
        ValueError: an unknown t-norm, frame or system family; ``max_worlds < 1``.
        NotImplementedError: the product t-norm; a frame with a condition that has no
            graded form here.
    """
    caller = "fuzzy_modal_search"
    if max_worlds < 1:
        raise ValueError(f"{caller}: max_worlds must be at least 1, got {max_worlds}.")
    ops = _z3_tnorm_ops(tnorm)
    for family in systems or {}:
        if family not in ("epistemic", "doxastic"):
            raise ValueError(
                f"{caller}: unknown system family {family!r} (use epistemic / doxastic).")
    relations = _relations_of(formula)
    conditions = {relation: _conditions(relation, frame, systems, caller)
                  for relation in ("alethic",) + relations}
    from ..semantics.tnorm import get_tnorm
    individuals = None if domain is None else frozenset(domain)
    universes = (None if sort_universes is None else
                 {sort: frozenset(names) for sort, names in sort_universes.items()})
    declared = _declared_names(individuals, universes)

    def unsupported(exc: Exception) -> FuzzyModalSearchResult:
        return FuzzyModalSearchResult(
            model=None, degree=None, exhausted=False, worlds=0,
            unsupported=f"{type(exc).__name__}: {exc}",
            detail="the formula is outside the fragment this search decides")

    decided = 0
    for size in range(1, max_worlds + 1):
        reading = _Unknown(size)
        try:
            _refuse_parameters(formula, caller)
            check_sorted_constants(formula, universes, caller)
            encoder = _Encoder(reading, tnorm, caller, individuals, universes)
            expr, constraints = encoder.open_degree(formula, 0)
            encoder.refuse_coreference(declared)
        except (NotImplementedError, TypeError, ValueError) as exc:
            return unsupported(exc)
        for relation in relations:
            constraints += _frame_constraints(reading, relation, conditions[relation], ops)
        for real in list(reading.weights.values()):
            constraints += [real >= 0, real <= 1]
            if crisp_frame:
                constraints.append(Z3Or(real == 0, real == 1))
        for real in reading.degrees.values():
            constraints += [real >= 0, real <= 1]

        solver = _solver(constraints, timeout)
        solver.add(expr < 1)
        outcome = solver.check()
        if outcome == unsat:
            decided = size
            continue
        if outcome != sat:
            return FuzzyModalSearchResult(
                model=None, degree=None, exhausted=False, worlds=decided,
                detail=(f"Z3 did not decide the models with {size} world(s) within "
                        f"{timeout} ms ({outcome}); the search up to "
                        f"max_worlds={max_worlds} did not complete"),
                timed_out=True)
        values = solver.model()
        # A countermodel by a wide margin, where there is one: its degree stays below 1
        # when the rationals become floats.
        wide = _solver(constraints, timeout)
        wide.add(2 * expr <= 1)
        if wide.check() == sat:
            values = wide.model()

        def number(real: ArithRef) -> float:
            return float(_rng_value(values, real))

        weights: Dict[str, Dict[Tuple[int, int], float]] = {name: {} for name in relations}
        for (relation, source, target), real in reading.weights.items():
            weights[relation][(source, target)] = number(real)
        valuation: Dict[int, Dict[str, float]] = {world: {} for world in reading.worlds}
        for (world, key), real in reading.degrees.items():
            valuation[world][key] = number(real)
        model = FuzzyKripkeModel(reading.worlds, weights, valuation, tnorm=get_tnorm(tnorm),
                                 domain=individuals, sort_universes=universes)
        degree = satisfies_fuzzy_modal(formula, model, 0)
        if not degree < 1.0:
            return FuzzyModalSearchResult(
                model=None, degree=None, exhausted=False, worlds=decided,
                detail=(f"Z3 found a countermodel with {size} world(s) in exact arithmetic "
                        "whose degree is not below 1 when its weights and degrees are "
                        "floats; no model is reported"))
        return FuzzyModalSearchResult(
            model=model, degree=degree, exhausted=False, worlds=size,
            detail=f"countermodel with {size} world(s): degree {degree} at world 0")

    return FuzzyModalSearchResult(
        model=None, degree=None, exhausted=True, worlds=decided,
        detail=(f"no countermodel with at most {max_worlds} world(s); not a proof of "
                "validity, larger models are not searched"))


def fuzzy_modal_countermodel(formula: Node, **options: Any) -> Optional[FuzzyKripkeModel]:
    """The countermodel :func:`fuzzy_modal_search` finds, or ``None``.

    ``None`` does not tell "no countermodel up to the bound" from "not decided in time"
    and from "outside the fragment"; :func:`fuzzy_modal_search` does.
    """
    return fuzzy_modal_search(formula, **options).model
