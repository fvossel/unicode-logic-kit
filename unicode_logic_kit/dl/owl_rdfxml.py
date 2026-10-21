"""Read an OWL 2 ontology published as **RDF/XML** into a TBox/ABox, with every
refusal as data.

Ontologies are published as RDF/XML (the OBO Foundry's ENVO and ChEBI, the Open
Energy Ontology, ...). :func:`parse_owl_rdfxml` reads such a file as it is, with
no Docker, no Java and no third-party package, and returns an
:class:`OwlRdfResult`. That class IS an
:class:`~unicode_logic_kit.dl.owl_functional.OwlFunctionalResult` (``tbox``,
``abox``, ``refused``, ``accepted``, ``skipped``, ``consumed``, ``ok``,
``refused_keywords``, ``to_kb()``) with seven more fields: ``axioms``,
``iris``, ``functional_text``, ``annotations``, ``deprecated``, ``imports`` and
``ontology_iri``.

``axioms`` holds the accepted axioms one by one, as :class:`AcceptedAxiom`
objects: its Functional-Syntax text, its keyword and the entity its triple is
about. A TBox does not say which inclusions came from which axiom (one
``EquivalentClasses`` is two of them); an axiom's own text read alone,
``parse_owl_functional_axioms("Ontology(" + axiom.text + ")").to_kb()``, is its
own FOL image.

Two steps
---------
1. **RDF/XML to triples**, by the grammar of the W3C recommendation *RDF 1.1
   XML Syntax*: node and property elements, ``rdf:about`` / ``rdf:ID`` /
   ``rdf:nodeID``, typed node elements, property attributes, ``rdf:resource``,
   ``rdf:datatype``, ``xml:lang``, ``xml:base``, ``rdf:parseType`` ``"Resource"``
   / ``"Collection"`` / ``"Literal"``, ``rdf:li``, and the reification an
   ``rdf:ID`` on a property element states. The XML is read by the standard
   library's parser, which expands the entities a document declares in its DTD
   (``&obo;``, the form Protégé and the OWL API write) and fetches no external
   entity. A relative IRI is resolved by RFC 3986, section 5.2, against the
   ``xml:base`` in scope, else the ``base`` argument, else the file's own
   ``file:`` IRI. The document is read as a stream: each node element directly
   under ``rdf:RDF`` is turned into its triples when its end tag is read and is
   then dropped, so the XML tree of a whole large ontology is never held.
2. **Triples to axioms**, by the reverse of the W3C mapping (*OWL 2 Web
   Ontology Language Mapping to RDF Graphs*, section 3): the declarations first,
   then one axiom per axiom triple or axiom node, with the class expressions,
   data ranges and inverse properties the blank nodes spell read where an axiom
   uses them. Each axiom is written as OWL 2 Functional-Style text and the whole
   text is read by
   :func:`~unicode_logic_kit.dl.owl_functional.parse_owl_functional_axioms`. So
   the fragment that is read, the axioms that are refused and the words they are
   refused with are that reader's, by construction: an RDF/XML document and its
   Functional-Syntax rendering give the same knowledge base.

``functional_text`` is that Functional-Syntax document; the ``position`` of a
refusal or of a consumed axiom that step 2's reader reports is an offset into it.
A named class with ``owl:intersectionOf`` / ``owl:unionOf`` /
``owl:complementOf`` / ``owl:oneOf`` of its own (the OWL 1 form of a complete
class definition) is read as ``EquivalentClasses`` of the class and the
expression, which is what such a triple states.

What the mapping itself refuses
-------------------------------
A triple with no OWL 2 reading is reported, never dropped: one
:class:`~unicode_logic_kit.dl.owl_functional.RefusedAxiom` each, after the
refusals of step 2, with ``position == -1``, ``keyword`` the RDF term at fault
(``"rdf:type"``, ``"rdfs:subPropertyOf"``, ...), ``text`` the triple in
N-Triples form and ``reason`` the cause. The causes:

- a predicate that is no OWL 2 vocabulary and is not declared as an object, data
  or annotation property: the declaration is what makes the triple an object
  property assertion, a data property assertion or an annotation;
- an axiom whose reading depends on the kind of a property the document does not
  declare and no well-typed reading decides: ``rdfs:domain``,
  ``owl:FunctionalProperty``, an unqualified cardinality, a property that is
  declared as two kinds. Where only one reading is well typed it is taken: the
  filler of a restriction tells an object property from a data property
  (annotation properties occur in no restriction), one declared side of
  ``rdfs:subPropertyOf`` / ``owl:equivalentProperty`` /
  ``owl:propertyDisjointWith`` gives the other side its kind, the range of
  ``rdfs:range`` tells a class from a datatype, and a property chain or one of
  the characteristics only object properties have makes an object property;
- ``rdf:type`` of something that is not a declared class or a class expression;
- a malformed construct: an RDF list that does not end in ``rdf:nil``, a
  restriction without ``owl:onProperty`` or with no filler or two, a cardinality
  that is not a non-negative integer, an intersection or union with fewer than
  two members, a blank node reached from itself;
- an n-ary data restriction (``owl:onProperties``), which the Functional-Syntax
  reader has no form for;
- every triple left over at the end that no construct read (a restriction no
  axiom uses, the reification an ``rdf:ID`` on a property element states, ...).

Annotations
-----------
Not logical axioms, so skipped and counted in ``annotations``: an annotation
assertion (a triple whose predicate is an annotation property, declared or one
of the nine OWL 2 has built in: ``rdfs:label``, ``rdfs:comment``,
``rdfs:seeAlso``, ``rdfs:isDefinedBy``, ``owl:deprecated``, ``owl:versionInfo``,
``owl:priorVersion``, ``owl:backwardCompatibleWith``,
``owl:incompatibleWith``), an annotation of the ontology, and each annotation
on a reified axiom (an ``owl:Axiom`` or ``owl:Annotation`` node, the form
``oboInOwl:hasDbXref`` on a definition takes; the copy of a class expression
such a node points to is read with it). None of them is written into
``functional_text``. ``skipped`` adds the declarations, the annotation
assertions and the ontology annotations to what the Functional-Syntax reader
skipped, so it counts what that reader counts for the full rendering (an
annotation on a reified axiom sits inside its axiom there and is not counted).
An entity annotated ``owl:deprecated true`` (or typed ``owl:DeprecatedClass`` /
``owl:DeprecatedProperty``) is listed in ``deprecated``; its axioms are read
like any other. ``owl:imports`` is listed in ``imports`` and NOT followed: the
axioms of an imported ontology are not in the result.

Names
-----
``names="local"`` (the default) names an entity by the local name of its IRI,
the part after the last ``#`` or ``/``
(``http://purl.obolibrary.org/obo/ENVO_01000201`` is ``ENVO_01000201``), and by
the full IRI when the local name is empty, holds a ``:``, or is also the local
name of another IRI the result names. ``names="iri"`` names every entity by its
full IRI, which is what the Functional-Syntax reader stores for ``<...>``.
Either way ``iris`` maps every name the result uses to its IRI, one to one. The
vocabulary of OWL 2 itself keeps its prefixed spelling (``owl:Thing``,
``xsd:integer``, ``owl:topObjectProperty``), by which the Functional-Syntax
reader recognises it. A blank node standing for an individual is written
``_:...``, and the Functional-Syntax reader refuses anonymous individuals by
name.

Not supported
-------------
RDF/XML is read, not Turtle, N-Triples or OWL/XML. The XML literal of
``rdf:parseType="Literal"`` is the element content as the XML library writes it,
not its exclusive canonical form (it only ever matters for an annotation).
Malformed XML and XML that is not RDF/XML raise :class:`OwlRdfXmlSyntaxError`.
"""

import bisect
import os
import re
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from itertools import count
from pathlib import Path
from typing import (
    Callable, Dict, Iterable, Iterator, List, Mapping, NamedTuple, Optional, Set, Tuple,
    TypeGuard, Union, cast,
)

from .datatypes import is_builtin_datatype
from .owl_functional import OwlFunctionalResult, RefusedAxiom, parse_owl_functional_axioms

__all__ = ["parse_owl_rdfxml", "OwlRdfResult", "AcceptedAxiom", "OwlRdfXmlSyntaxError"]

RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
RDFS = "http://www.w3.org/2000/01/rdf-schema#"
OWL = "http://www.w3.org/2002/07/owl#"
XSD = "http://www.w3.org/2001/XMLSchema#"
_XML = "http://www.w3.org/XML/1998/namespace"

_TYPE = RDF + "type"
_FIRST = RDF + "first"
_REST = RDF + "rest"
_NIL = RDF + "nil"


class OwlRdfXmlSyntaxError(ValueError):
    """The document is not well-formed XML, or it is XML that is not RDF/XML
    (an element or attribute with no namespace, text where a node element
    belongs, two node elements as one property value, ...)."""


# --------------------------------------------------------------------------- #
# Terms and IRIs.
# --------------------------------------------------------------------------- #

class _Literal(NamedTuple):
    lexical: str
    datatype: Optional[str] = None
    language: Optional[str] = None


# An IRI is a str, a blank node is a str starting with "_:" (no IRI does: a
# scheme starts with a letter), a literal is a _Literal.
_Term = Union[str, _Literal]
_Triple = Tuple[str, str, _Term]


def _is_blank(term: _Term) -> TypeGuard[str]:
    return isinstance(term, str) and term.startswith("_:")


# RFC 3986, Appendix B: the five components of a URI reference, each None when
# it is ABSENT (which differs from present and empty for the authority, the
# query and the fragment).
_COMPONENTS = re.compile(r"^(?:([^:/?#]+):)?(?://([^/?#]*))?([^?#]*)(?:\?([^#]*))?(?:#(.*))?$",
                         re.DOTALL)


def _components(ref: str):
    match = _COMPONENTS.match(ref)
    assert match is not None        # every part is optional: any string matches
    return match.groups()


def _remove_dot_segments(path: str) -> str:
    """RFC 3986, section 5.2.4, step by step (rules A to E)."""
    out = ""
    while path:
        if path.startswith("../"):
            path = path[3:]
        elif path.startswith("./"):
            path = path[2:]
        elif path.startswith("/./"):
            path = path[2:]
        elif path == "/.":
            path = "/"
        elif path.startswith("/../"):
            path = path[3:]
            out = out[:max(out.rfind("/"), 0)]
        elif path == "/..":
            path = "/"
            out = out[:max(out.rfind("/"), 0)]
        elif path in (".", ".."):
            path = ""
        else:
            end = path.find("/", 1)
            if end == -1:
                end = len(path)
            out += path[:end]
            path = path[end:]
    return out


def _recompose(scheme, authority, path, query, fragment) -> str:
    out = "" if scheme is None else scheme + ":"
    if authority is not None:
        out += "//" + authority
    out += path
    if query is not None:
        out += "?" + query
    if fragment is not None:
        out += "#" + fragment
    return out


def _resolve(base: str, ref: str) -> str:
    """``ref`` resolved against ``base`` by RFC 3986, section 5.2.2 (strict).

    With no base a relative reference stays as it is written.
    """
    scheme, authority, path, query, fragment = _components(ref)
    if scheme is not None:
        if "/." not in path and not path.startswith("."):
            return ref                      # nothing to remove: ref is already T
        return _recompose(scheme, authority, _remove_dot_segments(path), query, fragment)
    if not base:
        return ref
    b_scheme, b_authority, b_path, b_query, _ = _components(base)
    if authority is not None:
        return _recompose(b_scheme, authority, _remove_dot_segments(path), query, fragment)
    if path == "":
        return _recompose(b_scheme, b_authority, b_path,
                          query if query is not None else b_query, fragment)
    if path.startswith("/"):
        merged = path
    elif b_authority is not None and b_path == "":
        merged = "/" + path
    else:
        merged = b_path[:b_path.rfind("/") + 1] + path
    return _recompose(b_scheme, b_authority, _remove_dot_segments(merged), query, fragment)


# --------------------------------------------------------------------------- #
# Step 1: RDF/XML -> triples (RDF 1.1 XML Syntax, section 7).
# --------------------------------------------------------------------------- #

_ABOUT = "{%s}about" % RDF
_ID = "{%s}ID" % RDF
_NODE_ID = "{%s}nodeID" % RDF
_RESOURCE = "{%s}resource" % RDF
_DATATYPE = "{%s}datatype" % RDF
_PARSE_TYPE = "{%s}parseType" % RDF
_TYPE_ATTR = "{%s}type" % RDF
_XML_BASE = "{%s}base" % _XML
_XML_LANG = "{%s}lang" % _XML
_SYNTAX_ATTRS = frozenset({_ABOUT, _ID, _NODE_ID, _RESOURCE, _DATATYPE, _PARSE_TYPE})


def _qname_iri(name: str, what: str) -> str:
    """The IRI an ElementTree name ``{namespace}local`` stands for."""
    if not name.startswith("{"):
        raise OwlRdfXmlSyntaxError(
            f"the {what} {name!r} has no namespace, and RDF/XML gives no IRI to "
            f"a name without one")
    namespace, _, local = name[1:].partition("}")
    return namespace + local


def _has_text(text: Optional[str]) -> bool:
    return text is not None and text.strip() != ""


class _TripleReader:
    """The RDF/XML grammar over an ElementTree, collecting the triples."""

    def __init__(self) -> None:
        self.triples: List[_Triple] = []
        self._blanks = count()
        # one string object per IRI and blank node, however often it occurs
        self._terms: Dict[str, str] = {}

    def _fresh(self) -> str:
        return f"_:g{next(self._blanks)}"

    def _add(self, s: str, p: str, o: _Term) -> None:
        terms = self._terms
        s = terms.setdefault(s, s)
        p = terms.setdefault(p, p)
        if isinstance(o, str):
            o = terms.setdefault(o, o)
        self.triples.append((s, p, o))

    @staticmethod
    def _scope(elem, base: str, lang: Optional[str]) -> Tuple[str, Optional[str]]:
        given = elem.attrib.get(_XML_BASE)
        if given is not None:
            base = _resolve(base, given).partition("#")[0]
        given_lang = elem.attrib.get(_XML_LANG)
        if given_lang is not None:
            lang = given_lang or None
        return base, lang

    def document(self, events: Iterator[Tuple[str, ET.Element]], base: str) -> None:
        """The document whose ``start`` / ``end`` events the parser yields.

        A node element directly under ``rdf:RDF`` is read at its end tag and is
        removed from the tree at the next one, once its tail is known."""
        root = next(events)[1]
        depth = 1
        lang: Optional[str] = None
        is_rdf = root.tag == "{%s}RDF" % RDF
        if is_rdf:
            base, lang = self._scope(root, base, None)
        previous: Optional[ET.Element] = None
        for event, elem in events:
            if event == "start":
                depth += 1
                continue
            depth -= 1
            if not is_rdf:
                if depth == 0:
                    self.node(root, base, None)
                continue
            if depth > 1:
                continue
            # the text up to this end tag: before the first node element it is
            # rdf:RDF's own text, after one it is that element's tail
            if _has_text(root.text if previous is None else previous.tail):
                raise OwlRdfXmlSyntaxError("text directly inside rdf:RDF, where only node elements belong")
            if previous is not None:
                root.remove(previous)
            if depth == 1:
                self.node(elem, base, lang)
                previous = elem

    def node(self, elem, base: str, lang: Optional[str]) -> str:
        """A node element; returns its subject."""
        base, lang = self._scope(elem, base, lang)
        attrs = elem.attrib
        named = [key for key in (_ABOUT, _ID, _NODE_ID) if key in attrs]
        if len(named) > 1:
            raise OwlRdfXmlSyntaxError(
                f"a node element carries more than one of rdf:about, rdf:ID and "
                f"rdf:nodeID: {sorted(named)}")
        if _ABOUT in attrs:
            subject = _resolve(base, attrs[_ABOUT])
        elif _ID in attrs:
            subject = _resolve(base, "#" + attrs[_ID])
        elif _NODE_ID in attrs:
            subject = "_:n" + attrs[_NODE_ID]
        else:
            subject = self._fresh()
        kind = _qname_iri(elem.tag, "element")
        if kind != RDF + "Description":
            self._add(subject, _TYPE, kind)
        for key, value in attrs.items():
            if key in (_ABOUT, _ID, _NODE_ID) or key.startswith("{%s}" % _XML):
                continue
            if key in _SYNTAX_ATTRS:
                raise OwlRdfXmlSyntaxError(
                    f"the attribute {key!r} belongs on a property element, not on a node element")
            prop = _qname_iri(key, "attribute")
            if prop == _TYPE:
                self._add(subject, _TYPE, _resolve(base, value))
            else:
                self._add(subject, prop, _Literal(value, None, lang))
        if _has_text(elem.text):
            raise OwlRdfXmlSyntaxError(
                f"text inside the node element of {subject}, where only property elements belong")
        items = count(1)
        for child in elem:
            self.property(subject, child, base, lang, items)
            if _has_text(child.tail):
                raise OwlRdfXmlSyntaxError(
                    f"text inside the node element of {subject}, where only property elements belong")
        return subject

    def property(self, subject: str, elem, base: str, lang: Optional[str], items) -> None:
        """A property element of ``subject``."""
        base, lang = self._scope(elem, base, lang)
        prop = _qname_iri(elem.tag, "element")
        if prop == RDF + "li":
            prop = f"{RDF}_{next(items)}"
        attrs = elem.attrib
        children = list(elem)
        parse_type = attrs.get(_PARSE_TYPE)
        obj: _Term
        if parse_type == "Resource":
            obj = self._fresh()
            self._add(subject, prop, obj)
            inner = count(1)
            for child in children:
                self.property(obj, child, base, lang, inner)
        elif parse_type == "Collection":
            members = [self.node(child, base, lang) for child in children]
            obj = self._list(members)
            self._add(subject, prop, obj)
        elif parse_type is not None:
            # "Literal", and every other value (RDF 1.1 XML Syntax, 7.2.20).
            content = (elem.text or "") + "".join(
                ET.tostring(child, encoding="unicode") for child in children)
            obj = _Literal(content, RDF + "XMLLiteral")
            self._add(subject, prop, obj)
        elif children:
            if len(children) > 1 or _has_text(elem.text) or any(
                    _has_text(child.tail) for child in children):
                raise OwlRdfXmlSyntaxError(
                    f"the property element {prop} of {subject} holds more than one "
                    f"node element, or text beside one")
            obj = self.node(children[0], base, lang)
            self._add(subject, prop, obj)
        else:
            extra = [(key, value) for key, value in attrs.items()
                     if key not in _SYNTAX_ATTRS and not key.startswith("{%s}" % _XML)]
            if _RESOURCE in attrs or _NODE_ID in attrs or extra:
                if _has_text(elem.text) or _DATATYPE in attrs:
                    raise OwlRdfXmlSyntaxError(
                        f"the property element {prop} of {subject} names a resource "
                        f"and holds a literal")
                if _RESOURCE in attrs and _NODE_ID in attrs:
                    raise OwlRdfXmlSyntaxError(
                        f"the property element {prop} of {subject} carries both "
                        f"rdf:resource and rdf:nodeID")
                if _RESOURCE in attrs:
                    node = _resolve(base, attrs[_RESOURCE])
                elif _NODE_ID in attrs:
                    node = "_:n" + attrs[_NODE_ID]
                else:
                    node = self._fresh()
                obj = node
                self._add(subject, prop, node)
                for key, value in extra:
                    inner_prop = _qname_iri(key, "attribute")
                    if inner_prop == _TYPE:
                        self._add(node, _TYPE, _resolve(base, value))
                    else:
                        self._add(node, inner_prop, _Literal(value, None, lang))
            else:
                text = elem.text or ""
                if _DATATYPE in attrs:
                    obj = _Literal(text, _resolve(base, attrs[_DATATYPE]), None)
                else:
                    obj = _Literal(text, None, lang)
                self._add(subject, prop, obj)
        if _ID in attrs:
            statement = _resolve(base, "#" + attrs[_ID])
            self._add(statement, _TYPE, RDF + "Statement")
            self._add(statement, RDF + "subject", subject)
            self._add(statement, RDF + "predicate", prop)
            self._add(statement, RDF + "object", obj)

    def _list(self, members: List[str]) -> str:
        if not members:
            return _NIL
        cells = [self._fresh() for _ in members]
        for i, (cell, member) in enumerate(zip(cells, members)):
            self._add(cell, _FIRST, member)
            self._add(cell, _REST, cells[i + 1] if i + 1 < len(cells) else _NIL)
        return cells[0]


_CHUNK = 1 << 16


def _file_chunks(path: Path) -> Iterator[bytes]:
    with open(path, "rb") as handle:
        while True:
            chunk = handle.read(_CHUNK)
            if not chunk:
                return
            yield chunk


def _events(chunks: Iterable[Union[str, bytes]]) -> Iterator[Tuple[str, ET.Element]]:
    """The ``start`` and ``end`` events of the XML the chunks spell, as it is read."""
    parser: "ET.XMLPullParser[ET.Element]" = ET.XMLPullParser(events=("start", "end"))
    # each of these two events comes with its element (only the namespace events
    # the stub's wider type also covers do not)
    read = cast(Callable[[], Iterator[Tuple[str, ET.Element]]], parser.read_events)
    for chunk in chunks:
        parser.feed(chunk)
        yield from read()
    parser.close()
    yield from read()


def _read_triples(source, base: Optional[str] = None) -> List[_Triple]:
    """The triples of an RDF/XML document: a path, the text, or its bytes."""
    chunks: Iterable[Union[str, bytes]]
    if isinstance(source, os.PathLike) or (
            isinstance(source, str) and not source.lstrip("\ufeff \t\r\n").startswith("<")):
        path = Path(source)
        chunks = _file_chunks(path)
        document_base = base or path.resolve().as_uri()
    elif isinstance(source, (str, bytes)):
        chunks = (source[i:i + _CHUNK] for i in range(0, len(source), _CHUNK))
        document_base = base or ""
    else:
        raise TypeError(f"parse_owl_rdfxml takes a path, the document's text or its "
                        f"bytes, not {type(source).__name__}")
    reader = _TripleReader()
    try:
        reader.document(_events(chunks), document_base)
    except ET.ParseError as exc:
        raise OwlRdfXmlSyntaxError(f"not well-formed XML: {exc}") from exc
    return reader.triples


# --------------------------------------------------------------------------- #
# Step 2: triples -> OWL 2 axioms as Functional-Style text (OWL 2 Mapping to
# RDF Graphs, section 3).
# --------------------------------------------------------------------------- #

_DECLARATIONS = {
    OWL + "Class": "Class", RDFS + "Datatype": "Datatype",
    OWL + "ObjectProperty": "ObjectProperty", OWL + "DatatypeProperty": "DataProperty",
    OWL + "AnnotationProperty": "AnnotationProperty", OWL + "NamedIndividual": "NamedIndividual",
}
_KIND_OF_DECLARATION = {"ObjectProperty": "object", "DataProperty": "data",
                        "AnnotationProperty": "annotation"}
_BUILTIN_ANNOTATION_PROPERTIES = frozenset({
    RDFS + "label", RDFS + "comment", RDFS + "seeAlso", RDFS + "isDefinedBy",
    OWL + "deprecated", OWL + "versionInfo", OWL + "priorVersion",
    OWL + "backwardCompatibleWith", OWL + "incompatibleWith",
})
_BUILTIN_PROPERTY_KINDS = {
    OWL + "topObjectProperty": "object", OWL + "bottomObjectProperty": "object",
    OWL + "topDataProperty": "data", OWL + "bottomDataProperty": "data",
    **{iri: "annotation" for iri in _BUILTIN_ANNOTATION_PROPERTIES},
}
# The characteristics only an object property has, with their axiom keyword.
_OBJECT_CHARACTERISTICS = {
    OWL + "InverseFunctionalProperty": "InverseFunctionalObjectProperty",
    OWL + "TransitiveProperty": "TransitiveObjectProperty",
    OWL + "SymmetricProperty": "SymmetricObjectProperty",
    OWL + "AsymmetricProperty": "AsymmetricObjectProperty",
    OWL + "ReflexiveProperty": "ReflexiveObjectProperty",
    OWL + "IrreflexiveProperty": "IrreflexiveObjectProperty",
}
# rdf:type objects of a node that is read as part of something else.
_STRUCTURAL_TYPES = frozenset({
    OWL + "Restriction", RDF + "List", OWL + "Axiom", OWL + "Annotation",
})
_CLASS_OPERATORS = (OWL + "intersectionOf", OWL + "unionOf", OWL + "complementOf", OWL + "oneOf")
_RESTRICTION_FILLERS = (
    OWL + "someValuesFrom", OWL + "allValuesFrom", OWL + "hasValue", OWL + "hasSelf",
    OWL + "minCardinality", OWL + "maxCardinality", OWL + "cardinality",
    OWL + "minQualifiedCardinality", OWL + "maxQualifiedCardinality",
    OWL + "qualifiedCardinality",
)
_CARDINALITY_KEYWORDS = {
    "minCardinality": "MinCardinality", "maxCardinality": "MaxCardinality",
    "cardinality": "ExactCardinality", "minQualifiedCardinality": "MinCardinality",
    "maxQualifiedCardinality": "MaxCardinality", "qualifiedCardinality": "ExactCardinality",
}
# Predicates that only ever occur inside a construct an axiom reads.
_STRUCTURAL_PREDICATES = frozenset({
    _FIRST, _REST, OWL + "onProperty", OWL + "onProperties", OWL + "onClass",
    OWL + "onDataRange", OWL + "datatypeComplementOf", OWL + "onDatatype",
    OWL + "withRestrictions", OWL + "members", OWL + "distinctMembers",
    OWL + "sourceIndividual", OWL + "assertionProperty", OWL + "targetIndividual",
    OWL + "targetValue", OWL + "annotatedSource", OWL + "annotatedProperty",
    OWL + "annotatedTarget", *_RESTRICTION_FILLERS,
})
_INTEGER_DATATYPES = (None, XSD + "nonNegativeInteger", XSD + "integer")
_PREFIXES = (("owl:", OWL), ("rdfs:", RDFS), ("rdf:", RDF), ("xsd:", XSD))
_PREFIXED_LOCAL = re.compile(r"[A-Za-z_][A-Za-z0-9_.\-]*\Z")
_PLACEHOLDER = re.compile("\x00([0-9]+)\x01")


def _builtin_spelling(iri: str) -> Optional[str]:
    """The prefixed spelling of an IRI in the OWL, RDF, RDFS or XSD namespace."""
    for prefix, namespace in _PREFIXES:
        if iri.startswith(namespace) and _PREFIXED_LOCAL.match(iri, len(namespace)):
            return prefix + iri[len(namespace):]
    return None


def _local_name(iri: str) -> Optional[str]:
    cut = max(iri.rfind("#"), iri.rfind("/"))
    local = iri[cut + 1:] if cut >= 0 else ""
    return local if local and ":" not in local else None


def _ntriples_term(term: _Term) -> str:
    if isinstance(term, _Literal):
        text = '"' + (term.lexical.replace("\\", "\\\\").replace('"', '\\"')
                      .replace("\n", "\\n").replace("\r", "\\r")) + '"'
        if term.language:
            return f"{text}@{term.language}"
        return f"{text}^^<{term.datatype}>" if term.datatype else text
    return term if _is_blank(term) else f"<{term}>"


def _ntriple(triple: _Triple) -> str:
    return " ".join(_ntriples_term(t) for t in triple) + " ."


def _short(iri: str) -> str:
    return _builtin_spelling(iri) or iri


class _Refusal(Exception):
    """An axiom the mapping cannot write, with the RDF term at fault."""

    def __init__(self, keyword: str, reason: str):
        super().__init__(reason)
        self.keyword = keyword
        self.reason = reason


class _Mapper:
    def __init__(self, triples: List[_Triple]):
        self.triples = list(dict.fromkeys(triples))      # an RDF graph is a set
        self.by_subject: Dict[str, List[Tuple[str, _Term]]] = {}
        for s, p, o in self.triples:
            self.by_subject.setdefault(s, []).append((p, o))
        self.used: Set[_Triple] = set()
        self.kinds: Dict[str, Set[str]] = {}
        self.axioms: List[Tuple[str, Optional[str]]] = []      # (text, IRI it is about)
        self.refused: List[RefusedAxiom] = []
        self.vocabulary: Dict[str, int] = {}
        self.declarations = 0
        self.annotation_assertions = 0
        self.annotations = 0
        self.deprecated: List[str] = []
        self.imports: List[str] = []
        self.ontology_iri: Optional[str] = None
        self._reified: List[str] = []
        self._memo: Dict[str, str] = {}
        self._active: Set[str] = set()
        self._order = {triple: i for i, triple in enumerate(self.triples)}
        self._set = self._order.keys()

    # -- reading the graph -------------------------------------------------- #

    def values(self, s: str, p: str) -> List[_Term]:
        return [o for q, o in self.by_subject.get(s, ()) if q == p]

    def use(self, s: str, p: str, o: _Term) -> None:
        self.used.add((s, p, o))

    def take_one(self, s: str, p: str, what: str) -> _Term:
        found = self.values(s, p)
        if len(found) != 1:
            raise _Refusal(_short(p), f"{what} {s} has {len(found)} values for "
                                      f"{_short(p)}, where OWL 2 has exactly one")
        self.use(s, p, found[0])
        return found[0]

    def rdf_list(self, head: _Term, what: str) -> List[_Term]:
        members: List[_Term] = []
        seen: Set[str] = set()
        cell = head
        while cell != _NIL:
            if not _is_blank(cell) or cell in seen:
                raise _Refusal("rdf:List", f"the RDF list of {what} is not a list of blank "
                                           f"nodes ending in rdf:nil (at {_ntriples_term(cell)})")
            seen.add(cell)
            members.append(self.take_one(cell, _FIRST, "the list cell"))
            nxt = self.take_one(cell, _REST, "the list cell")
            if (cell, _TYPE, RDF + "List") in self._set:
                self.use(cell, _TYPE, RDF + "List")
            cell = nxt
        return members

    # -- names ---------------------------------------------------------------- #

    def ref(self, iri: str) -> str:
        """The Functional-Syntax token of an entity IRI (a placeholder until the
        names are decided, for an IRI outside the OWL 2 vocabulary)."""
        builtin = _builtin_spelling(iri)
        if builtin is not None:
            self.vocabulary.setdefault(iri, len(self.vocabulary))
            return builtin
        if ">" in iri or any(ch.isspace() for ch in iri):
            raise _Refusal("IRI", f"the IRI {iri!r} holds '>' or white space and has no "
                                  f"Functional-Syntax spelling")
        index = self.vocabulary.setdefault(iri, len(self.vocabulary))
        return f"\x00{index}\x01"

    # -- kinds ---------------------------------------------------------------- #

    def kind(self, term: _Term) -> Optional[str]:
        """``"object"``, ``"data"``, ``"annotation"`` or None (not declared)."""
        if isinstance(term, _Literal):
            return None
        if _is_blank(term):
            return "object" if self.values(term, OWL + "inverseOf") else None
        if term in _BUILTIN_PROPERTY_KINDS:
            return _BUILTIN_PROPERTY_KINDS[term]
        declared = sorted({_KIND_OF_DECLARATION[k] for k in self.kinds.get(term, ())
                           if k in _KIND_OF_DECLARATION})
        if len(declared) > 1:
            raise _Refusal("Declaration", f"{term} is declared as {' and as '.join(declared)} "
                                          f"property, and OWL 2 DL keeps those apart")
        return declared[0] if declared else None

    def is_class(self, term: _Term) -> bool:
        if isinstance(term, _Literal):
            return False
        if _is_blank(term):
            types = self.values(term, _TYPE)
            if RDFS + "Datatype" in types or OWL + "DataRange" in types:
                return False
            return (OWL + "Class" in types or OWL + "Restriction" in types
                    or any(self.values(term, p) for p in _CLASS_OPERATORS[:3])
                    or any(not isinstance(m, _Literal) for m in self._members(term, OWL + "oneOf")))
        return term in (OWL + "Thing", OWL + "Nothing") or "Class" in self.kinds.get(term, ())

    def is_data_range(self, term: _Term) -> bool:
        if isinstance(term, _Literal):
            return False
        if _is_blank(term):
            types = self.values(term, _TYPE)
            if RDFS + "Datatype" in types or OWL + "DataRange" in types:
                return True
            return bool(self.values(term, OWL + "datatypeComplementOf")
                        or self.values(term, OWL + "onDatatype")
                        or any(isinstance(m, _Literal) for m in self._members(term, OWL + "oneOf")))
        builtin = _builtin_spelling(term)
        return (builtin is not None and is_builtin_datatype(builtin)) or \
            "Datatype" in self.kinds.get(term, ())

    def _members(self, node: str, p: str) -> List[_Term]:
        """The members of the list under ``p``, without marking anything read."""
        heads = self.values(node, p)
        if len(heads) != 1:
            return []
        out: List[_Term] = []
        cell, seen = heads[0], set()
        while _is_blank(cell) and cell not in seen:
            seen.add(cell)
            out.extend(self.values(cell, _FIRST)[:1])
            rest = self.values(cell, _REST)
            cell = rest[0] if rest else _NIL
        return out

    # -- expressions ---------------------------------------------------------- #

    def _enter(self, node: str) -> None:
        if node in self._active:
            raise _Refusal("blank node", f"the blank node {node} is reached from itself")
        self._active.add(node)

    def ce(self, term: _Term) -> str:
        """A class expression."""
        if isinstance(term, _Literal):
            raise _Refusal("class expression", f"the literal {_ntriples_term(term)} stands "
                                               f"where a class expression belongs")
        if not _is_blank(term):
            return self.ref(term)
        if term in self._memo:
            return self._memo[term]
        if self.is_data_range(term):
            raise _Refusal("class expression", f"the data range {term} stands where a "
                                               f"class expression belongs")
        self._enter(term)
        try:
            types = self.values(term, _TYPE)
            if OWL + "Restriction" in types:
                text = self._restriction(term)
            else:
                operators = [p for p in _CLASS_OPERATORS if self.values(term, p)]
                if len(operators) != 1:
                    raise _Refusal("class expression", f"the blank node {term} is no class "
                                                       f"expression: it has {len(operators)} of "
                                                       f"owl:intersectionOf / owl:unionOf / "
                                                       f"owl:complementOf / owl:oneOf")
                if OWL + "Class" in types:
                    self.use(term, _TYPE, OWL + "Class")
                text = self._class_operator(term, operators[0],
                                            self.take_one(term, operators[0], "the class expression"))
        finally:
            self._active.discard(term)
        self._memo[term] = text
        return text

    def _class_operator(self, node: str, p: str, value: _Term) -> str:
        if p == OWL + "complementOf":
            return f"ObjectComplementOf({self.ce(value)})"
        members = self.rdf_list(value, f"{_short(p)} of {node}")
        if p == OWL + "oneOf":
            if not members:
                raise _Refusal("owl:oneOf", f"owl:oneOf of {node} has no member")
            return f"ObjectOneOf({' '.join(self.individual(m) for m in members)})"
        if len(members) < 2:
            raise _Refusal(_short(p), f"{_short(p)} of {node} has {len(members)} member(s), "
                                      f"where OWL 2 has at least two")
        keyword = "ObjectIntersectionOf" if p == OWL + "intersectionOf" else "ObjectUnionOf"
        return f"{keyword}({' '.join(self.ce(m) for m in members)})"

    def _restriction(self, node: str) -> str:
        self.use(node, _TYPE, OWL + "Restriction")
        if self.values(node, OWL + "onProperties"):
            raise _Refusal("owl:onProperties", f"the restriction {node} is an n-ary data "
                                               f"restriction (owl:onProperties), which "
                                               f"the Functional-Syntax reader has no form for")
        prop = self.take_one(node, OWL + "onProperty", "the restriction")
        fillers = [p for p in _RESTRICTION_FILLERS if self.values(node, p)]
        if len(fillers) != 1:
            raise _Refusal("owl:Restriction", f"the restriction {node} has {len(fillers)} "
                                              f"fillers, where OWL 2 has exactly one")
        p = fillers[0]
        value = self.take_one(node, p, "the restriction")
        local = p[len(OWL):]
        kind = self.kind(prop)
        if kind == "annotation":
            raise _Refusal("owl:onProperty", f"the restriction {node} is on the annotation "
                                             f"property {prop}")
        if local in ("someValuesFrom", "allValuesFrom"):
            keyword = "SomeValuesFrom" if local == "someValuesFrom" else "AllValuesFrom"
            if kind is None:
                kind = ("object" if self.is_class(value)
                        else "data" if self.is_data_range(value) else None)
            if kind is None:
                raise _Refusal("owl:onProperty", f"the property {prop} of the restriction "
                                                 f"{node} is not declared, and its filler "
                                                 f"is neither a class nor a data range")
            if kind == "object":
                return f"Object{keyword}({self.ope(prop)} {self.ce(value)})"
            return f"Data{keyword}({self.dpe(prop)} {self.data_range(value)})"
        if local == "hasValue":
            if isinstance(value, _Literal):
                if kind == "object":
                    raise _Refusal("owl:hasValue", f"the object property {prop} has the "
                                                   f"literal value {_ntriples_term(value)}")
                return f"DataHasValue({self.dpe(prop)} {self.literal(value)})"
            if kind == "data":
                raise _Refusal("owl:hasValue", f"the data property {prop} has the "
                                               f"individual value {value}")
            return f"ObjectHasValue({self.ope(prop)} {self.individual(value)})"
        if local == "hasSelf":
            if not (isinstance(value, _Literal) and value.lexical.strip() in ("true", "1")):
                raise _Refusal("owl:hasSelf", f"owl:hasSelf of {node} is not true")
            if kind == "data":
                raise _Refusal("owl:hasSelf", f"the data property {prop} in a self restriction")
            return f"ObjectHasSelf({self.ope(prop)})"
        number = self._cardinality(node, p, value)
        keyword = _CARDINALITY_KEYWORDS[local]
        if local.endswith("QualifiedCardinality") or local == "qualifiedCardinality":
            on_class = self.values(node, OWL + "onClass")
            on_range = self.values(node, OWL + "onDataRange")
            if len(on_class) + len(on_range) != 1:
                raise _Refusal(_short(p), f"the qualified restriction {node} has "
                                          f"{len(on_class) + len(on_range)} of owl:onClass / "
                                          f"owl:onDataRange, where OWL 2 has exactly one")
            if on_class:
                if kind == "data":
                    raise _Refusal("owl:onClass", f"the data property {prop} with owl:onClass")
                self.use(node, OWL + "onClass", on_class[0])
                return f"Object{keyword}({number} {self.ope(prop)} {self.ce(on_class[0])})"
            if kind == "object":
                raise _Refusal("owl:onDataRange", f"the object property {prop} with owl:onDataRange")
            self.use(node, OWL + "onDataRange", on_range[0])
            return f"Data{keyword}({number} {self.dpe(prop)} {self.data_range(on_range[0])})"
        if kind is None:
            raise _Refusal("owl:onProperty", f"the property {prop} of the cardinality "
                                             f"restriction {node} is not declared, so "
                                             f"whether it counts individuals or data values "
                                             f"is not decided")
        if kind == "object":
            return f"Object{keyword}({number} {self.ope(prop)})"
        return f"Data{keyword}({number} {self.dpe(prop)})"

    @staticmethod
    def _cardinality(node: str, p: str, value: _Term) -> int:
        if (isinstance(value, _Literal) and value.datatype in _INTEGER_DATATYPES
                and re.fullmatch(r"\+?[0-9]+", value.lexical.strip())):
            return int(value.lexical.strip())
        raise _Refusal(_short(p), f"{_short(p)} of {node} is {_ntriples_term(value)}, "
                                  f"not a non-negative integer")

    def data_range(self, term: _Term) -> str:
        if isinstance(term, _Literal):
            raise _Refusal("data range", f"the literal {_ntriples_term(term)} stands where "
                                         f"a data range belongs")
        if not _is_blank(term):
            return self.ref(term)
        if term in self._memo:
            return self._memo[term]
        if self.is_class(term):
            raise _Refusal("data range", f"the class expression {term} stands where a "
                                         f"data range belongs")
        self._enter(term)
        try:
            for declared in (RDFS + "Datatype", OWL + "DataRange"):
                if declared in self.values(term, _TYPE):
                    self.use(term, _TYPE, declared)
            operators = [p for p in (OWL + "intersectionOf", OWL + "unionOf",
                                     OWL + "datatypeComplementOf", OWL + "oneOf",
                                     OWL + "onDatatype") if self.values(term, p)]
            if len(operators) != 1:
                raise _Refusal("data range", f"the blank node {term} is no data range: it "
                                             f"has {len(operators)} data range operators")
            p = operators[0]
            value = self.take_one(term, p, "the data range")
            if p == OWL + "datatypeComplementOf":
                text = f"DataComplementOf({self.data_range(value)})"
            elif p == OWL + "onDatatype":
                text = self._datatype_restriction(term, value)
            else:
                members = self.rdf_list(value, f"{_short(p)} of {term}")
                if p == OWL + "oneOf":
                    if not members:
                        raise _Refusal("owl:oneOf", f"owl:oneOf of {term} has no member")
                    text = f"DataOneOf({' '.join(self.literal(m) for m in members)})"
                else:
                    if len(members) < 2:
                        raise _Refusal(_short(p), f"{_short(p)} of {term} has {len(members)} "
                                                  f"member(s), where OWL 2 has at least two")
                    keyword = "DataIntersectionOf" if p == OWL + "intersectionOf" else "DataUnionOf"
                    text = f"{keyword}({' '.join(self.data_range(m) for m in members)})"
        finally:
            self._active.discard(term)
        self._memo[term] = text
        return text

    def _datatype_restriction(self, node: str, datatype: _Term) -> str:
        if not isinstance(datatype, str) or _is_blank(datatype):
            raise _Refusal("owl:onDatatype", f"owl:onDatatype of {node} is not a datatype IRI")
        restrictions = self.take_one(node, OWL + "withRestrictions", "the datatype restriction")
        parts = []
        for facet_node in self.rdf_list(restrictions, f"owl:withRestrictions of {node}"):
            pairs = self.by_subject.get(facet_node, []) if _is_blank(facet_node) else []
            if not _is_blank(facet_node) or len(pairs) != 1 or not isinstance(pairs[0][1], _Literal):
                raise _Refusal("owl:withRestrictions", f"the facet {facet_node} of {node} is "
                                                       f"not one (facet, literal) pair")
            facet, value = pairs[0]
            self.use(facet_node, facet, value)
            parts.append(f"{self.ref(facet)} {self.literal(value)}")
        if not parts:
            raise _Refusal("owl:withRestrictions", f"the datatype restriction {node} has no facet")
        return f"DatatypeRestriction({self.ref(datatype)} {' '.join(parts)})"

    def ope(self, term: _Term) -> str:
        """An object property expression."""
        if isinstance(term, _Literal):
            raise _Refusal("property", f"the literal {_ntriples_term(term)} stands where an "
                                       f"object property belongs")
        if not _is_blank(term):
            if self.kind(term) not in (None, "object"):
                raise _Refusal("property", f"the {self.kind(term)} property {term} stands "
                                           f"where an object property belongs")
            return self.ref(term)
        inner = self.take_one(term, OWL + "inverseOf", "the inverse property")
        if not isinstance(inner, str) or _is_blank(inner):
            raise _Refusal("owl:inverseOf", f"the inverse property {term} is not the inverse "
                                            f"of a property IRI")
        return f"ObjectInverseOf({self.ope(inner)})"

    def dpe(self, term: _Term) -> str:
        if not isinstance(term, str) or _is_blank(term):
            raise _Refusal("property", f"{_ntriples_term(term)} stands where a data "
                                       f"property belongs")
        return self.ref(term)

    def iri(self, term: _Term, what: str) -> str:
        """An IRI in an annotation-property axiom."""
        if not isinstance(term, str) or _is_blank(term):
            raise _Refusal(what, f"{_ntriples_term(term)} stands where {what} has an IRI")
        return self.ref(term)

    def individual(self, term: _Term) -> str:
        if isinstance(term, _Literal):
            raise _Refusal("individual", f"the literal {_ntriples_term(term)} stands where "
                                         f"an individual belongs")
        return term if _is_blank(term) else self.ref(term)

    def literal(self, term: _Term) -> str:
        if not isinstance(term, _Literal):
            raise _Refusal("literal", f"{_ntriples_term(term)} stands where a literal belongs")
        text = '"' + term.lexical.replace("\\", "\\\\").replace('"', '\\"') + '"'
        if term.language:
            return f"{text}@{term.language}"
        if term.datatype is None:
            return text
        return f"{text}^^{self.ref(term.datatype)}"

    # -- the passes ----------------------------------------------------------- #

    def run(self) -> None:
        self._declarations()
        self._header()
        self._reifications()
        for triple in self.triples:
            if triple in self.used:
                continue
            try:
                self._axiom(triple)
            except _Refusal as refusal:
                self._refuse(triple, refusal.keyword, refusal.reason)
        self._reification_copies()
        for triple in self.triples:
            if triple not in self.used:
                self._refuse(triple, *self._leftover(triple))

    def _refuse(self, triple: _Triple, keyword: str, reason: str) -> None:
        """Report ``triple`` with the blank-node structure under it (its
        ``text`` holds all of them, one N-Triples line each), and mark them read."""
        self.used.add(triple)
        under = self._use_closure([t for t in (triple[0], triple[2]) if _is_blank(t)])
        text = "\n".join(_ntriple(t) for t in [triple] + [t for t in under if t != triple])
        self.refused.append(RefusedAxiom(keyword=keyword, position=-1, text=text, reason=reason))

    def _use_closure(self, stack: List[str]) -> List[_Triple]:
        """Mark read every triple of the blank nodes reachable from ``stack``
        through blank nodes, and return them in document order."""
        seen: Set[str] = set()
        reached: Set[_Triple] = set()
        while stack:
            node = stack.pop()
            if node in seen:
                continue
            seen.add(node)
            for p, o in self.by_subject.get(node, ()):
                reached.add((node, p, o))
                if _is_blank(o):
                    stack.append(o)
        self.used.update(reached)
        return sorted(reached, key=self._order.__getitem__)

    def _declarations(self) -> None:
        for s, p, o in self.triples:
            if p != _TYPE or _is_blank(s) or not isinstance(o, str):
                continue
            if o in _DECLARATIONS:
                self.kinds.setdefault(s, set()).add(_DECLARATIONS[o])
                self.declarations += 1
                self.use(s, p, o)
            elif o in (OWL + "DeprecatedClass", OWL + "DeprecatedProperty"):
                if o == OWL + "DeprecatedClass":
                    self.kinds.setdefault(s, set()).add("Class")
                    self.declarations += 1
                self._deprecate(s)
                self.annotations += 1
                self.annotation_assertions += 1
                self.use(s, p, o)
        # A characteristic only an object property has makes an undeclared
        # property an object property (the one well-typed reading).
        for s, p, o in self.triples:
            if p == _TYPE and o in _OBJECT_CHARACTERISTICS and not _is_blank(s):
                found = self.kinds.setdefault(s, set())
                if not found & {"DataProperty", "AnnotationProperty"}:
                    found.add("ObjectProperty")

    def _deprecate(self, iri: str) -> None:
        if iri not in self.deprecated:
            self.deprecated.append(iri)

    def _header(self) -> None:
        for s, p, o in self.triples:
            if p == _TYPE and o == OWL + "Ontology":
                self.use(s, p, o)
                if self.ontology_iri is None and not _is_blank(s):
                    self.ontology_iri = s
                for q, value in self.by_subject.get(s, ()):
                    if q == OWL + "imports" and isinstance(value, str):
                        self.imports.append(value)
                        self.use(s, q, value)
                    elif q == OWL + "versionIRI":
                        self.use(s, q, value)
                    elif q != _TYPE and self._is_annotation_property(q):
                        self.annotations += 1
                        self.annotation_assertions += 1
                        self.use(s, q, value)

    def _is_annotation_property(self, p: str) -> bool:
        try:
            return self.kind(p) == "annotation"
        except _Refusal:
            return False

    def _reifications(self) -> None:
        structure = (_TYPE, OWL + "annotatedSource", OWL + "annotatedProperty",
                     OWL + "annotatedTarget")
        for s, p, o in self.triples:
            if p == _TYPE and o in (OWL + "Axiom", OWL + "Annotation"):
                for q, value in self.by_subject.get(s, ()):
                    if q not in structure and not self._is_annotation_property(q):
                        continue
                    self.use(s, q, value)
                    if q not in structure:
                        self.annotations += 1
                    elif q in (OWL + "annotatedSource", OWL + "annotatedTarget") and _is_blank(value):
                        self._reified.append(value)

    def _reification_copies(self) -> None:
        """The blank nodes a reified axiom points to and no axiom read: the copy
        of a class expression the OWL API writes for an annotated axiom."""
        stack = [node for node in self._reified
                 if any((node, p, o) not in self.used for p, o in self.by_subject.get(node, ()))]
        self._use_closure(stack)

    def _emit(self, text: str, triple: _Triple) -> None:
        """One axiom, from ``triple`` and the constructs it reaches; the
        subject of an axiom triple (not of an axiom node) is what it is about."""
        subject = triple[0]
        about = None if _is_blank(subject) else subject
        self.axioms.append((text, about))
        self.used.add(triple)

    def _axiom(self, triple: _Triple) -> None:
        s, p, o = triple
        if p == _TYPE:
            self._typing(triple)
            return
        handler = _AXIOM_PREDICATES.get(p)
        if handler is not None:
            handler(self, triple)
            return
        if p in _STRUCTURAL_PREDICATES or p in _CLASS_OPERATORS or p == OWL + "inverseOf":
            return              # read with the construct it belongs to, or left over
        kind = self.kind(p)
        if kind == "annotation":
            self.annotations += 1
            self.annotation_assertions += 1
            self.use(s, p, o)
            if (p == OWL + "deprecated" and isinstance(o, _Literal)
                    and o.lexical.strip() in ("true", "1") and not _is_blank(s)):
                self._deprecate(s)
        elif kind == "object":
            self._emit(f"ObjectPropertyAssertion({self.ope(p)} {self.individual(s)} "
                       f"{self.individual(o)})", triple)
        elif kind == "data":
            self._emit(f"DataPropertyAssertion({self.dpe(p)} {self.individual(s)} "
                       f"{self.literal(o)})", triple)

    def _typing(self, triple: _Triple) -> None:
        s, _, o = triple
        if not isinstance(o, str) or (_is_blank(s) and o in (OWL + "Class", RDFS + "Datatype",
                                                             OWL + "DataRange")):
            return
        if o in _STRUCTURAL_TYPES:
            return
        if o in _OBJECT_CHARACTERISTICS:
            if self.kind(s) not in (None, "object"):
                raise _Refusal("rdf:type", f"{_short(o)} of the {self.kind(s)} property {s}")
            self._emit(f"{_OBJECT_CHARACTERISTICS[o]}({self.ope(s)})", triple)
        elif o == OWL + "FunctionalProperty":
            kind = self.kind(s)
            if kind == "object":
                self._emit(f"FunctionalObjectProperty({self.ope(s)})", triple)
            elif kind == "data":
                self._emit(f"FunctionalDataProperty({self.dpe(s)})", triple)
            else:
                raise _Refusal("rdf:type", f"owl:FunctionalProperty of {s}, which is not "
                                           f"declared as an object or a data property")
        elif o == OWL + "AllDisjointClasses":
            members = self._node_list(s, OWL + "members")
            self._emit(f"DisjointClasses({' '.join(self.ce(m) for m in members)})", triple)
        elif o == OWL + "AllDifferent":
            heads = [p for p in (OWL + "members", OWL + "distinctMembers") if self.values(s, p)]
            if len(heads) != 1:
                raise _Refusal("owl:AllDifferent", f"owl:AllDifferent {s} has {len(heads)} of "
                                                   f"owl:members / owl:distinctMembers")
            members = self._node_list(s, heads[0])
            self._emit(f"DifferentIndividuals({' '.join(self.individual(m) for m in members)})",
                       triple)
        elif o == OWL + "AllDisjointProperties":
            members = self._node_list(s, OWL + "members")
            # One declared kind gives the undeclared members theirs (the one
            # well-typed reading), as for a pair of properties.
            kinds = {self.kind(m) for m in members} - {None}
            if kinds == {"object"}:
                self._emit(f"DisjointObjectProperties({' '.join(self.ope(m) for m in members)})",
                           triple)
            elif kinds == {"data"}:
                self._emit(f"DisjointDataProperties({' '.join(self.dpe(m) for m in members)})",
                           triple)
            else:
                raise _Refusal("owl:AllDisjointProperties",
                               f"owl:AllDisjointProperties {s} lists properties of the kinds "
                               f"{sorted(str(k) for k in kinds)}, not all object or all data "
                               f"properties")
        elif o == OWL + "NegativePropertyAssertion":
            self._negative_assertion(triple)
        elif self.is_class(o):
            self._emit(f"ClassAssertion({self.ce(o)} {self.individual(s)})", triple)
        else:
            raise _Refusal("rdf:type", f"rdf:type {_short(o)}: {_short(o)} is not declared "
                                       f"as a class, so the triple has no OWL 2 reading")

    def _node_list(self, node: str, p: str) -> List[_Term]:
        members = self.rdf_list(self.take_one(node, p, "the axiom node"), f"{_short(p)} of {node}")
        if len(members) < 2:
            raise _Refusal(_short(p), f"{_short(p)} of {node} has {len(members)} member(s), "
                                      f"where OWL 2 has at least two")
        return members

    def _negative_assertion(self, triple: _Triple) -> None:
        node = triple[0]
        source = self.take_one(node, OWL + "sourceIndividual", "the negative assertion")
        prop = self.take_one(node, OWL + "assertionProperty", "the negative assertion")
        targets = [p for p in (OWL + "targetIndividual", OWL + "targetValue") if self.values(node, p)]
        if len(targets) != 1:
            raise _Refusal("owl:NegativePropertyAssertion",
                           f"the negative assertion {node} has {len(targets)} of "
                           f"owl:targetIndividual / owl:targetValue")
        target = self.take_one(node, targets[0], "the negative assertion")
        if targets[0] == OWL + "targetValue":
            self._emit(f"NegativeDataPropertyAssertion({self.dpe(prop)} {self.individual(source)} "
                       f"{self.literal(target)})", triple)
        else:
            self._emit(f"NegativeObjectPropertyAssertion({self.ope(prop)} "
                       f"{self.individual(source)} {self.individual(target)})", triple)

    def _leftover(self, triple: _Triple) -> Tuple[str, str]:
        s, p, o = triple
        if p == _TYPE:
            return "rdf:type", (f"rdf:type {_ntriples_term(o)} of {s} is part of no construct "
                                f"an OWL 2 axiom reads")
        if p in _STRUCTURAL_PREDICATES or p in _CLASS_OPERATORS or p == OWL + "inverseOf":
            return _short(p), (f"{_short(p)} of {s} is part of no construct an OWL 2 axiom "
                               f"reads (a class expression, data range or list no axiom uses)")
        if _builtin_spelling(p) is not None:
            return _short(p), f"{_short(p)} has no OWL 2 reading here"
        return _short(p), (f"the predicate {p} is neither OWL 2 vocabulary nor declared as an "
                           f"object, data or annotation property, so the triple is no OWL 2 "
                           f"axiom")

    # -- the triples that are axioms ----------------------------------------- #

    def _sub_class(self, triple: _Triple) -> None:
        s, _, o = triple
        self._emit(f"SubClassOf({self.ce(s)} {self.ce(o)})", triple)

    def _equivalent_class(self, triple: _Triple) -> None:
        s, _, o = triple
        if isinstance(s, str) and not _is_blank(s) and "Datatype" in self.kinds.get(s, ()):
            self._emit(f"DatatypeDefinition({self.ref(s)} {self.data_range(o)})", triple)
        else:
            self._emit(f"EquivalentClasses({self.ce(s)} {self.ce(o)})", triple)

    def _disjoint_with(self, triple: _Triple) -> None:
        s, _, o = triple
        self._emit(f"DisjointClasses({self.ce(s)} {self.ce(o)})", triple)

    def _disjoint_union(self, triple: _Triple) -> None:
        s, p, o = triple
        members = self.rdf_list(o, f"owl:disjointUnionOf of {s}")
        if len(members) < 2:
            raise _Refusal("owl:disjointUnionOf", f"owl:disjointUnionOf of {s} has "
                                                  f"{len(members)} member(s)")
        self._emit(f"DisjointUnion({self.ref(s)} {' '.join(self.ce(m) for m in members)})", triple)

    def _has_key(self, triple: _Triple) -> None:
        s, _, o = triple
        members = self.rdf_list(o, f"owl:hasKey of {s}")
        objects, data = [], []
        for member in members:
            kind = self.kind(member)
            if kind == "object":
                objects.append(self.ope(member))
            elif kind == "data":
                data.append(self.dpe(member))
            else:
                raise _Refusal("owl:hasKey", f"the key property {member} of {s} is not declared "
                                             f"as an object or a data property")
        self._emit(f"HasKey({self.ce(s)} ({' '.join(objects)}) ({' '.join(data)}))", triple)

    def _pair_kind(self, triple: _Triple) -> str:
        s, p, o = triple
        kinds = {k for k in (self.kind(s), self.kind(o)) if k is not None}
        if len(kinds) == 1:
            return kinds.pop()
        if not kinds:
            raise _Refusal(_short(p), f"{_short(p)} between {s} and {o}, neither of them "
                                      f"declared as an object, data or annotation property")
        raise _Refusal(_short(p), f"{_short(p)} between {s} and {o}, declared as properties "
                                  f"of different kinds ({' and '.join(sorted(kinds))})")

    def _sub_property(self, triple: _Triple) -> None:
        s, _, o = triple
        kind = self._pair_kind(triple)
        if kind == "object":
            self._emit(f"SubObjectPropertyOf({self.ope(s)} {self.ope(o)})", triple)
        elif kind == "data":
            self._emit(f"SubDataPropertyOf({self.dpe(s)} {self.dpe(o)})", triple)
        else:
            self._emit(f"SubAnnotationPropertyOf({self.iri(s, 'rdfs:subPropertyOf')} "
                       f"{self.iri(o, 'rdfs:subPropertyOf')})", triple)

    def _chain(self, triple: _Triple) -> None:
        s, _, o = triple
        members = self.rdf_list(o, f"owl:propertyChainAxiom of {s}")
        if len(members) < 2:
            raise _Refusal("owl:propertyChainAxiom", f"the property chain of {s} has "
                                                     f"{len(members)} member(s), where OWL 2 "
                                                     f"has at least two")
        chain = " ".join(self.ope(m) for m in members)
        self._emit(f"SubObjectPropertyOf(ObjectPropertyChain({chain}) {self.ope(s)})", triple)

    def _inverse(self, triple: _Triple) -> None:
        s, _, o = triple
        if _is_blank(s):
            return                  # an inverse property expression, read where it is used
        self._emit(f"InverseObjectProperties({self.ope(s)} {self.ope(o)})", triple)

    def _domain_or_range(self, triple: _Triple) -> None:
        s, p, o = triple
        which = "Domain" if p == RDFS + "domain" else "Range"
        kind = self.kind(s)
        if kind is None and which == "Range" and not _is_blank(s):
            kind = ("object" if self.is_class(o)
                    else "data" if self.is_data_range(o) else None)
        if kind is None and _is_blank(s):
            kind = "object"
        if kind == "object":
            self._emit(f"ObjectProperty{which}({self.ope(s)} {self.ce(o)})", triple)
        elif kind == "data":
            filler = self.ce(o) if which == "Domain" else self.data_range(o)
            self._emit(f"DataProperty{which}({self.dpe(s)} {filler})", triple)
        elif kind == "annotation":
            self._emit(f"AnnotationProperty{which}({self.iri(s, _short(p))} "
                       f"{self.iri(o, _short(p))})", triple)
        else:
            raise _Refusal(_short(p), f"{_short(p)} of {s}, which is not declared as an "
                                      f"object, data or annotation property")

    def _same_or_different(self, triple: _Triple) -> None:
        s, p, o = triple
        keyword = "SameIndividual" if p == OWL + "sameAs" else "DifferentIndividuals"
        self._emit(f"{keyword}({self.individual(s)} {self.individual(o)})", triple)

    def _named_class_operator(self, triple: _Triple) -> None:
        s, p, o = triple
        if _is_blank(s):
            return                  # a class expression, read where it is used
        self._emit(f"EquivalentClasses({self.ref(s)} {self._class_operator(s, p, o)})", triple)


def _property_pair(object_keyword: str, data_keyword: str):
    """The handler of ``owl:equivalentProperty`` / ``owl:propertyDisjointWith``."""
    def handler(mapper: _Mapper, triple: _Triple) -> None:
        s, p, o = triple
        kind = mapper._pair_kind(triple)
        if kind == "object":
            mapper._emit(f"{object_keyword}({mapper.ope(s)} {mapper.ope(o)})", triple)
        elif kind == "data":
            mapper._emit(f"{data_keyword}({mapper.dpe(s)} {mapper.dpe(o)})", triple)
        else:
            raise _Refusal(_short(p), f"{_short(p)} between the annotation properties "
                                      f"{s} and {o} has no OWL 2 reading")
    return handler


_AXIOM_PREDICATES = {
    RDFS + "subClassOf": _Mapper._sub_class,
    OWL + "equivalentClass": _Mapper._equivalent_class,
    OWL + "disjointWith": _Mapper._disjoint_with,
    OWL + "disjointUnionOf": _Mapper._disjoint_union,
    OWL + "hasKey": _Mapper._has_key,
    RDFS + "subPropertyOf": _Mapper._sub_property,
    OWL + "equivalentProperty": _property_pair(
        "EquivalentObjectProperties", "EquivalentDataProperties"),
    OWL + "propertyDisjointWith": _property_pair(
        "DisjointObjectProperties", "DisjointDataProperties"),
    OWL + "propertyChainAxiom": _Mapper._chain,
    OWL + "inverseOf": _Mapper._inverse,
    RDFS + "domain": _Mapper._domain_or_range,
    RDFS + "range": _Mapper._domain_or_range,
    OWL + "sameAs": _Mapper._same_or_different,
    OWL + "differentFrom": _Mapper._same_or_different,
    **{p: _Mapper._named_class_operator for p in _CLASS_OPERATORS},
}


# --------------------------------------------------------------------------- #
# The result and the entry point.
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class AcceptedAxiom:
    """One axiom :func:`parse_owl_rdfxml` read into the TBox/ABox, on its own.

    A TBox does not say which inclusions came from which axiom (one
    ``EquivalentClasses`` is two of them), so each accepted axiom is kept as its
    own Functional-Syntax text: ``parse_owl_functional_axioms("Ontology(" + text
    + ")")`` reads it alone, and ``.to_kb()`` of that is its FOL image.

    Fields: ``keyword`` (the axiom's Functional-Syntax keyword, ``"SubClassOf"``,
    ``"EquivalentClasses"``, ...), ``text`` (the axiom, with the names of the
    result), ``position`` (its offset in ``functional_text``) and ``subject``
    (the name of the entity the axiom's triple is about, ``A`` for ``A
    rdfs:subClassOf ...`` and the individual for an assertion; None for an
    axiom written as a node of its own, such as ``owl:AllDisjointClasses``, and
    for a class expression on the left of ``rdfs:subClassOf``).
    """

    keyword: str
    text: str
    position: int
    subject: Optional[str]


@dataclass(frozen=True)
class OwlRdfResult(OwlFunctionalResult):
    """What :func:`parse_owl_rdfxml` read from an RDF/XML document, and what it
    did not.

    Every field of :class:`~unicode_logic_kit.dl.owl_functional.OwlFunctionalResult`
    (see there), with ``refused`` holding the refusals of the Functional-Syntax
    reader first, in the order of ``functional_text``, and then those of the
    mapping (``position == -1``, see the module docstring). Seven more fields:

    * ``axioms`` — one :class:`AcceptedAxiom` per accepted axiom, in the order
      of ``functional_text`` (``len(axioms) == accepted``).
    * ``iris`` — every name the result uses (in ``tbox``, ``abox``,
      ``deprecated`` and ``functional_text``, declared entities included) to its
      IRI, one to one.
    * ``functional_text`` — the OWL 2 Functional-Style document the axioms were
      written as; refusal and consumed-axiom positions are offsets into it.
    * ``annotations`` — how many annotations were skipped: annotation
      assertions, ontology annotations and the annotations of reified axioms.
    * ``deprecated`` — the names of the entities annotated ``owl:deprecated
      true``, in document order.
    * ``imports`` — the IRIs of ``owl:imports``, which are not followed.
    * ``ontology_iri`` — the IRI of the ``owl:Ontology`` node, or None.
    """

    axioms: Tuple[AcceptedAxiom, ...] = ()
    iris: Mapping[str, str] = field(default_factory=dict)
    functional_text: str = ""
    annotations: int = 0
    deprecated: Tuple[str, ...] = ()
    imports: Tuple[str, ...] = ()
    ontology_iri: Optional[str] = None

    def to_dict(self) -> dict:
        """:meth:`OwlFunctionalResult.to_dict` plus ``axioms``, ``annotations``,
        ``deprecated``, ``imports``, ``ontology_iri`` and ``iris``."""
        out = super().to_dict()
        out.update({"axioms": [{"keyword": a.keyword, "text": a.text, "position": a.position,
                                "subject": a.subject} for a in self.axioms],
                    "annotations": self.annotations, "deprecated": list(self.deprecated),
                    "imports": list(self.imports), "ontology_iri": self.ontology_iri,
                    "iris": dict(self.iris)})
        return out


def _assign_names(vocabulary: Mapping[str, int], mode: str) -> Dict[str, str]:
    """IRI -> name, one to one (see "Names" in the module docstring)."""
    names: Dict[str, str] = {}
    by_local: Dict[str, List[str]] = {}
    for iri in vocabulary:
        builtin = _builtin_spelling(iri)
        local = _local_name(iri)
        if builtin is not None:
            names[iri] = builtin
        elif mode == "local" and local is not None:
            by_local.setdefault(local, []).append(iri)
        else:
            names[iri] = iri
    for local, iris in by_local.items():
        for iri in iris:
            names[iri] = local if len(iris) == 1 else iri
    return names


def _iter_names(text: str, names: Mapping[int, str]) -> Iterator[str]:
    position = 0
    for match in _PLACEHOLDER.finditer(text):
        yield text[position:match.start()]
        yield "<" + names[int(match.group(1))] + ">"
        position = match.end()
    yield text[position:]


def parse_owl_rdfxml(source: Union[str, bytes, "os.PathLike[str]"], *,
                     base: Optional[str] = None, names: str = "local") -> OwlRdfResult:
    """Read an OWL 2 ontology in RDF/XML, REPORTING what is outside the fragment.

    The RDF/XML counterpart of
    :func:`~unicode_logic_kit.dl.owl_functional.parse_owl_functional_axioms`, and
    the same result for the same ontology: the TBox and ABox of every axiom it
    could read, plus each axiom it could not, by name and with its reason (see
    the module docstring for the two steps, the refusals, the annotations and
    the names).

    Args:
        source: The document: a path (a ``str`` that does not start with ``<``,
            or an ``os.PathLike``), its text, or its bytes.
        base: The base IRI of the document, for its relative IRIs where no
            ``xml:base`` is in scope. Default: the file's ``file:`` IRI for a
            path, none for text (a relative IRI then stays as it is written).
        names: ``"local"`` (the default) to name an entity by the local name of
            its IRI where that is unique, ``"iri"`` to name it by its full IRI.

    Returns:
        An :class:`OwlRdfResult`. ``result.to_kb()`` is the FOL image, and
        ``result.iris`` maps its names back to the IRIs.

    Raises:
        OwlRdfXmlSyntaxError: for XML that is not well formed, or that is not
            RDF/XML. Never for an axiom outside the fragment: that is a
            refusal in the result.
        ValueError: for a ``names`` other than ``"local"`` and ``"iri"``.
    """
    if names not in ("local", "iri"):
        raise ValueError(f"names must be 'local' or 'iri', not {names!r}")
    mapper = _Mapper(_read_triples(source, base))
    mapper.run()
    # The declared and the deprecated entities are names of the result too.
    for iri in list(mapper.kinds) + mapper.deprecated:
        if ">" not in iri and not any(ch.isspace() for ch in iri):
            mapper.ref(iri)
    by_iri = _assign_names(mapper.vocabulary, names)
    by_index = {index: by_iri[iri] for iri, index in mapper.vocabulary.items()}
    head = "Ontology("
    if mapper.ontology_iri is not None and ">" not in mapper.ontology_iri:
        head += f"<{mapper.ontology_iri}>"
    # A name outside the OWL 2 vocabulary is written in angle brackets, which
    # the reader takes for a name whatever they hold; the vocabulary is bare.
    parts = [head + "\n"]
    length = len(parts[0])
    spans: List[Tuple[int, str, Optional[str]]] = []
    for written, about in mapper.axioms:
        axiom = "".join(_iter_names(written, by_index))
        spans.append((length, axiom, about))
        parts.append(axiom + "\n")
        length += len(axiom) + 1
    parts.append(")\n")
    text = "".join(parts)
    read = parse_owl_functional_axioms(text)
    # Each written axiom is one axiom of the text: it was refused if a refusal
    # points into it, consumed if a consumed axiom starts at it, else accepted.
    refused_at = sorted(r.position for r in read.refused)
    consumed_at = {c.position for c in read.consumed}
    accepted_axioms = []
    for start, axiom, about in spans:
        i = bisect.bisect_left(refused_at, start)
        if (i < len(refused_at) and refused_at[i] < start + len(axiom)) or start in consumed_at:
            continue
        accepted_axioms.append(AcceptedAxiom(
            keyword=axiom.partition("(")[0], text=axiom, position=start,
            subject=None if about is None else by_iri.get(about)))
    return OwlRdfResult(
        tbox=read.tbox, abox=read.abox, refused=read.refused + tuple(mapper.refused),
        accepted=read.accepted, axioms=tuple(accepted_axioms),
        skipped=read.skipped + mapper.declarations + mapper.annotation_assertions,
        consumed=read.consumed,
        iris={name: iri for iri, name in by_iri.items()},
        functional_text=text, annotations=mapper.annotations,
        deprecated=tuple(by_iri[iri] for iri in mapper.deprecated if iri in by_iri),
        imports=tuple(mapper.imports), ontology_iri=mapper.ontology_iri)
