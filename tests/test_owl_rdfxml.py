r"""Tests for ``dl.parse_owl_rdfxml``, the OWL 2 reader for RDF/XML.

The oracle for the mapping is the Functional-Syntax reader: an RDF/XML document
and its hand-written Functional-Syntax rendering must give the same TBox and
ABox, the same consumed axioms and the same refusals with the same reasons. The
RDF/XML grammar is checked against hand-derived triples (and against rdflib
where it is installed), IRI resolution against the examples of RFC 3986,
section 5.4.
"""

import collections
import dataclasses
import json
import re

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit.dl.owl_rdfxml import (
    OwlRdfResult, OwlRdfXmlSyntaxError, _Literal, _TripleReader, _events, _read_triples, _resolve,
    parse_owl_rdfxml,
)

RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
RDFS = "http://www.w3.org/2000/01/rdf-schema#"
OWL = "http://www.w3.org/2002/07/owl#"
XSD = "http://www.w3.org/2001/XMLSchema#"
EX = "http://example.org/o#"

HEAD = """<?xml version="1.0"?>
<!DOCTYPE rdf:RDF [
  <!ENTITY ex "http://example.org/o#">
  <!ENTITY xsd "http://www.w3.org/2001/XMLSchema#">
  <!ENTITY owl "http://www.w3.org/2002/07/owl#">
  <!ENTITY rdf "http://www.w3.org/1999/02/22-rdf-syntax-ns#">
]>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
         xmlns:owl="http://www.w3.org/2002/07/owl#"
         xmlns:xsd="http://www.w3.org/2001/XMLSchema#"
         xmlns:ex="http://example.org/o#">
"""

VOCABULARY = """
<owl:Class rdf:about="&ex;A"/><owl:Class rdf:about="&ex;B"/><owl:Class rdf:about="&ex;C"/>
<owl:ObjectProperty rdf:about="&ex;p"/><owl:ObjectProperty rdf:about="&ex;q"/>
<owl:ObjectProperty rdf:about="&ex;r"/>
<owl:DatatypeProperty rdf:about="&ex;d"/><owl:DatatypeProperty rdf:about="&ex;e"/>
<owl:AnnotationProperty rdf:about="&ex;note"/><owl:AnnotationProperty rdf:about="&ex;remark"/>
"""
#: The declarations VOCABULARY makes.
VOCABULARY_DECLARATIONS = 10


def document(body: str, vocabulary: bool = True) -> str:
    return HEAD + (VOCABULARY if vocabulary else "") + body + "\n</rdf:RDF>\n"


def sub_class(expression: str) -> str:
    return f'<owl:Class rdf:about="&ex;A"><rdfs:subClassOf>{expression}</rdfs:subClassOf></owl:Class>'


def restriction(prop: str, filler: str) -> str:
    return (f'<owl:Restriction><owl:onProperty rdf:resource="&{prop}"/>{filler}'
            f'</owl:Restriction>')


def card(name: str, n: int) -> str:
    return f'<owl:{name} rdf:datatype="&xsd;nonNegativeInteger">{n}</owl:{name}>'


FACET = ('<rdfs:Datatype><owl:onDatatype rdf:resource="&xsd;integer"/>'
         '<owl:withRestrictions rdf:parseType="Collection"><rdf:Description>'
         '<xsd:minInclusive rdf:datatype="&xsd;integer">0</xsd:minInclusive>'
         '</rdf:Description></owl:withRestrictions></rdfs:Datatype>')


# --------------------------------------------------------------------------- #
# The mapping: every construct reads as its Functional-Syntax rendering.
# --------------------------------------------------------------------------- #

CASES = [
    ("subclass", '<owl:Class rdf:about="&ex;A"><rdfs:subClassOf rdf:resource="&ex;B"/></owl:Class>',
     "SubClassOf(A B)"),
    ("equivalent intersection some",
     '<owl:Class rdf:about="&ex;A"><owl:equivalentClass><owl:Class>'
     '<owl:intersectionOf rdf:parseType="Collection"><rdf:Description rdf:about="&ex;B"/>'
     + restriction("ex;p", '<owl:someValuesFrom rdf:resource="&ex;C"/>')
     + '</owl:intersectionOf></owl:Class></owl:equivalentClass></owl:Class>',
     "EquivalentClasses(A ObjectIntersectionOf(B ObjectSomeValuesFrom(p C)))"),
    ("disjoint", '<owl:Class rdf:about="&ex;A"><owl:disjointWith rdf:resource="&ex;B"/></owl:Class>',
     "DisjointClasses(A B)"),
    ("union and complement",
     sub_class('<owl:Class><owl:unionOf rdf:parseType="Collection">'
               '<rdf:Description rdf:about="&ex;B"/><owl:Class>'
               '<owl:complementOf rdf:resource="&ex;C"/></owl:Class></owl:unionOf></owl:Class>'),
     "SubClassOf(A ObjectUnionOf(B ObjectComplementOf(C)))"),
    ("all values", sub_class(restriction("ex;p", '<owl:allValuesFrom rdf:resource="&ex;B"/>')),
     "SubClassOf(A ObjectAllValuesFrom(p B))"),
    ("has value", sub_class(restriction("ex;p", '<owl:hasValue rdf:resource="&ex;a"/>')),
     "SubClassOf(A ObjectHasValue(p a))"),
    ("min", sub_class(restriction("ex;p", card("minCardinality", 2))),
     "SubClassOf(A ObjectMinCardinality(2 p))"),
    ("max", sub_class(restriction("ex;p", card("maxCardinality", 1))),
     "SubClassOf(A ObjectMaxCardinality(1 p))"),
    ("exact", sub_class(restriction("ex;p", card("cardinality", 3))),
     "SubClassOf(A ObjectExactCardinality(3 p))"),
    ("min qualified", sub_class(restriction(
        "ex;p", card("minQualifiedCardinality", 1) + '<owl:onClass rdf:resource="&ex;B"/>')),
     "SubClassOf(A ObjectMinCardinality(1 p B))"),
    ("max qualified", sub_class(restriction(
        "ex;p", card("maxQualifiedCardinality", 2) + '<owl:onClass rdf:resource="&ex;B"/>')),
     "SubClassOf(A ObjectMaxCardinality(2 p B))"),
    ("exact qualified", sub_class(restriction(
        "ex;p", card("qualifiedCardinality", 1) + '<owl:onClass rdf:resource="&ex;B"/>')),
     "SubClassOf(A ObjectExactCardinality(1 p B))"),
    ("data some", sub_class(restriction("ex;d", '<owl:someValuesFrom rdf:resource="&xsd;integer"/>')),
     "SubClassOf(A DataSomeValuesFrom(d xsd:integer))"),
    ("data has value", sub_class(restriction(
        "ex;d", '<owl:hasValue rdf:datatype="&xsd;integer">5</owl:hasValue>')),
     'SubClassOf(A DataHasValue(d "5"^^xsd:integer))'),
    ("data max", sub_class(restriction("ex;d", card("maxCardinality", 1))),
     "SubClassOf(A DataMaxCardinality(1 d))"),
    ("data qualified", sub_class(restriction(
        "ex;d", card("minQualifiedCardinality", 1) + '<owl:onDataRange rdf:resource="&xsd;string"/>')),
     "SubClassOf(A DataMinCardinality(1 d xsd:string))"),
    ("data facet", sub_class(restriction("ex;d", f"<owl:allValuesFrom>{FACET}</owl:allValuesFrom>")),
     'SubClassOf(A DataAllValuesFrom(d DatatypeRestriction(xsd:integer xsd:minInclusive "0"^^xsd:integer)))'),
    ("data one of", sub_class(restriction(
        "ex;d", '<owl:someValuesFrom><rdfs:Datatype><owl:oneOf><rdf:Description>'
                '<rdf:first>red</rdf:first><rdf:rest rdf:resource="&rdf;nil"/>'
                '</rdf:Description></owl:oneOf></rdfs:Datatype></owl:someValuesFrom>')),
     'SubClassOf(A DataSomeValuesFrom(d DataOneOf("red")))'),
    ("data complement", sub_class(restriction(
        "ex;d", '<owl:someValuesFrom><rdfs:Datatype><owl:datatypeComplementOf '
                'rdf:resource="&xsd;string"/></rdfs:Datatype></owl:someValuesFrom>')),
     "SubClassOf(A DataSomeValuesFrom(d DataComplementOf(xsd:string)))"),
    ("named class with an intersection (OWL 1)",
     '<owl:Class rdf:about="&ex;A"><owl:intersectionOf rdf:parseType="Collection">'
     '<rdf:Description rdf:about="&ex;B"/><rdf:Description rdf:about="&ex;C"/>'
     '</owl:intersectionOf></owl:Class>',
     "EquivalentClasses(A ObjectIntersectionOf(B C))"),
    ("owl:Thing", '<owl:Class rdf:about="&ex;A"><rdfs:subClassOf rdf:resource="&owl;Thing"/></owl:Class>',
     "SubClassOf(A owl:Thing)"),
    ("sub object property", '<rdf:Description rdf:about="&ex;p"><rdfs:subPropertyOf rdf:resource="&ex;q"/></rdf:Description>',
     "SubObjectPropertyOf(p q)"),
    ("sub data property", '<rdf:Description rdf:about="&ex;d"><rdfs:subPropertyOf rdf:resource="&ex;e"/></rdf:Description>',
     "SubDataPropertyOf(d e)"),
    ("sub property of an inverse",
     '<rdf:Description rdf:about="&ex;p"><rdfs:subPropertyOf><rdf:Description>'
     '<owl:inverseOf rdf:resource="&ex;q"/></rdf:Description></rdfs:subPropertyOf></rdf:Description>',
     "SubObjectPropertyOf(p ObjectInverseOf(q))"),
    ("inverse properties", '<rdf:Description rdf:about="&ex;p"><owl:inverseOf rdf:resource="&ex;q"/></rdf:Description>',
     "InverseObjectProperties(p q)"),
    ("chain", '<rdf:Description rdf:about="&ex;r"><owl:propertyChainAxiom rdf:parseType="Collection">'
              '<rdf:Description rdf:about="&ex;p"/><rdf:Description rdf:about="&ex;q"/>'
              '</owl:propertyChainAxiom></rdf:Description>',
     "SubObjectPropertyOf(ObjectPropertyChain(p q) r)"),
    ("equivalent properties", '<rdf:Description rdf:about="&ex;p"><owl:equivalentProperty rdf:resource="&ex;q"/></rdf:Description>',
     "EquivalentObjectProperties(p q)"),
    ("disjoint properties", '<rdf:Description rdf:about="&ex;p"><owl:propertyDisjointWith rdf:resource="&ex;q"/></rdf:Description>',
     "DisjointObjectProperties(p q)"),
    ("disjoint data properties", '<rdf:Description rdf:about="&ex;d"><owl:propertyDisjointWith rdf:resource="&ex;e"/></rdf:Description>',
     "DisjointDataProperties(d e)"),
    *[(f"characteristic {name}",
       f'<rdf:Description rdf:about="&ex;p"><rdf:type rdf:resource="&owl;{name}"/></rdf:Description>',
       f"{keyword}(p)")
      for name, keyword in (("TransitiveProperty", "TransitiveObjectProperty"),
                            ("SymmetricProperty", "SymmetricObjectProperty"),
                            ("AsymmetricProperty", "AsymmetricObjectProperty"),
                            ("ReflexiveProperty", "ReflexiveObjectProperty"),
                            ("IrreflexiveProperty", "IrreflexiveObjectProperty"),
                            ("FunctionalProperty", "FunctionalObjectProperty"),
                            ("InverseFunctionalProperty", "InverseFunctionalObjectProperty"))],
    ("functional data property", '<rdf:Description rdf:about="&ex;d"><rdf:type rdf:resource="&owl;FunctionalProperty"/></rdf:Description>',
     "FunctionalDataProperty(d)"),
    ("object domain and range", '<rdf:Description rdf:about="&ex;p"><rdfs:domain rdf:resource="&ex;A"/>'
                                '<rdfs:range rdf:resource="&ex;B"/></rdf:Description>',
     "ObjectPropertyDomain(p A) ObjectPropertyRange(p B)"),
    ("data domain and range", '<rdf:Description rdf:about="&ex;d"><rdfs:domain rdf:resource="&ex;A"/>'
                              '<rdfs:range rdf:resource="&xsd;integer"/></rdf:Description>',
     "DataPropertyDomain(d A) DataPropertyRange(d xsd:integer)"),
    ("annotation property axioms",
     '<rdf:Description rdf:about="&ex;note"><rdfs:subPropertyOf rdf:resource="&ex;remark"/>'
     '<rdfs:domain rdf:resource="&ex;A"/><rdfs:range rdf:resource="&ex;B"/></rdf:Description>',
     "SubAnnotationPropertyOf(note remark) AnnotationPropertyDomain(note A) AnnotationPropertyRange(note B)"),
    ("class assertion", '<owl:NamedIndividual rdf:about="&ex;a"><rdf:type rdf:resource="&ex;A"/></owl:NamedIndividual>',
     "ClassAssertion(A a)"),
    ("typed node element", '<ex:A rdf:about="&ex;a"/>', "ClassAssertion(A a)"),
    ("class expression assertion",
     '<rdf:Description rdf:about="&ex;a"><rdf:type>'
     + restriction("ex;p", '<owl:someValuesFrom rdf:resource="&ex;B"/>') + '</rdf:type></rdf:Description>',
     "ClassAssertion(ObjectSomeValuesFrom(p B) a)"),
    ("object property assertion", '<rdf:Description rdf:about="&ex;a"><ex:p rdf:resource="&ex;b"/></rdf:Description>',
     "ObjectPropertyAssertion(p a b)"),
    ("data property assertion", '<rdf:Description rdf:about="&ex;a"><ex:d rdf:datatype="&xsd;integer">7</ex:d></rdf:Description>',
     'DataPropertyAssertion(d a "7"^^xsd:integer)'),
    ("plain and language literals", '<rdf:Description rdf:about="&ex;a"><ex:d>x "y" \\z</ex:d>'
                                    '<ex:e xml:lang="en">y</ex:e></rdf:Description>',
     'DataPropertyAssertion(d a "x \\"y\\" \\\\z") DataPropertyAssertion(e a "y"@en)'),
    ("same individual", '<rdf:Description rdf:about="&ex;a"><owl:sameAs rdf:resource="&ex;b"/></rdf:Description>',
     "SameIndividual(a b)"),
    ("different individuals", '<rdf:Description rdf:about="&ex;a"><owl:differentFrom rdf:resource="&ex;b"/></rdf:Description>',
     "DifferentIndividuals(a b)"),
    ("all different", '<owl:AllDifferent><owl:distinctMembers rdf:parseType="Collection">'
                      '<rdf:Description rdf:about="&ex;a"/><rdf:Description rdf:about="&ex;b"/>'
                      '<rdf:Description rdf:about="&ex;c"/></owl:distinctMembers></owl:AllDifferent>',
     "DifferentIndividuals(a b c)"),
    ("all disjoint classes", '<owl:AllDisjointClasses><owl:members rdf:parseType="Collection">'
                             '<rdf:Description rdf:about="&ex;A"/><rdf:Description rdf:about="&ex;B"/>'
                             '<rdf:Description rdf:about="&ex;C"/></owl:members></owl:AllDisjointClasses>',
     "DisjointClasses(A B C)"),
    ("all disjoint properties", '<owl:AllDisjointProperties><owl:members rdf:parseType="Collection">'
                                '<rdf:Description rdf:about="&ex;p"/><rdf:Description rdf:about="&ex;q"/>'
                                '<rdf:Description rdf:about="&ex;r"/></owl:members></owl:AllDisjointProperties>',
     "DisjointObjectProperties(p q r)"),
    ("negative object assertion",
     '<owl:NegativePropertyAssertion><owl:sourceIndividual rdf:resource="&ex;a"/>'
     '<owl:assertionProperty rdf:resource="&ex;p"/><owl:targetIndividual rdf:resource="&ex;b"/>'
     '</owl:NegativePropertyAssertion>',
     "NegativeObjectPropertyAssertion(p a b)"),
    ("negative data assertion",
     '<owl:NegativePropertyAssertion><owl:sourceIndividual rdf:resource="&ex;a"/>'
     '<owl:assertionProperty rdf:resource="&ex;d"/>'
     '<owl:targetValue rdf:datatype="&xsd;integer">3</owl:targetValue></owl:NegativePropertyAssertion>',
     'NegativeDataPropertyAssertion(d a "3"^^xsd:integer)'),
    ("datatype definition", f'<rdfs:Datatype rdf:about="&ex;age"><owl:equivalentClass>{FACET}'
                            f'</owl:equivalentClass></rdfs:Datatype>',
     'DatatypeDefinition(age DatatypeRestriction(xsd:integer xsd:minInclusive "0"^^xsd:integer))'),
    # Refused by the Functional-Syntax reader, in its words.
    ("one of", sub_class('<owl:Class><owl:oneOf rdf:parseType="Collection">'
                         '<rdf:Description rdf:about="&ex;a"/></owl:oneOf></owl:Class>'),
     "SubClassOf(A ObjectOneOf(a))"),
    ("has self", sub_class(restriction("ex;p", '<owl:hasSelf rdf:datatype="&xsd;boolean">true</owl:hasSelf>')),
     "SubClassOf(A ObjectHasSelf(p))"),
    ("inverse in a restriction",
     sub_class('<owl:Restriction><owl:onProperty><rdf:Description><owl:inverseOf rdf:resource="&ex;p"/>'
               '</rdf:Description></owl:onProperty><owl:someValuesFrom rdf:resource="&ex;B"/></owl:Restriction>'),
     "SubClassOf(A ObjectSomeValuesFrom(ObjectInverseOf(p) B))"),
    ("has key", '<owl:Class rdf:about="&ex;A"><owl:hasKey rdf:parseType="Collection">'
                '<rdf:Description rdf:about="&ex;p"/><rdf:Description rdf:about="&ex;d"/>'
                '</owl:hasKey></owl:Class>',
     "HasKey(A (p) (d))"),
    ("disjoint union", '<owl:Class rdf:about="&ex;A"><owl:disjointUnionOf rdf:parseType="Collection">'
                       '<rdf:Description rdf:about="&ex;B"/><rdf:Description rdf:about="&ex;C"/>'
                       '</owl:disjointUnionOf></owl:Class>',
     "DisjointUnion(A B C)"),
    ("universal property", sub_class(restriction("owl;topObjectProperty", '<owl:someValuesFrom rdf:resource="&ex;B"/>')),
     "SubClassOf(A ObjectSomeValuesFrom(owl:topObjectProperty B))"),
    ("anonymous individual", '<rdf:Description rdf:about="&ex;a"><ex:p><rdf:Description/></ex:p></rdf:Description>',
     "ObjectPropertyAssertion(p a _:x)"),
    ("float literal", '<rdf:Description rdf:about="&ex;a"><ex:d rdf:datatype="&xsd;float">1.5</ex:d></rdf:Description>',
     'DataPropertyAssertion(d a "1.5"^^xsd:float)'),
]


def _gist(reason: str) -> str:
    """A refusal reason without where it points (a position, the document and a
    blank node's label differ between the two documents)."""
    reason = re.sub(r" at position \d+", "", reason)
    reason = re.sub(r"'_:[^']*'", "'_:'", reason)
    return reason.rsplit(" in ", 1)[0]


def _keyword(keyword: str) -> str:
    return "_:" if keyword.startswith("_:") else keyword


def reads_like(body: str, functional: str) -> OwlRdfResult:
    got = parse_owl_rdfxml(document(body))
    want = dl.parse_owl_functional_axioms(f"Ontology({functional})")
    assert got.tbox == want.tbox
    assert got.abox == want.abox
    assert got.accepted == want.accepted
    assert [(c.keyword, c.reason) for c in got.consumed] == \
        [(c.keyword, c.reason) for c in want.consumed]
    assert [(_keyword(r.keyword), _gist(r.reason)) for r in got.refused] == \
        [(_keyword(r.keyword), _gist(r.reason)) for r in want.refused]
    each_axiom_reads_alone(got)
    return got


def each_axiom_reads_alone(result: OwlRdfResult) -> None:
    """Every accepted axiom, read on its own, is accepted, and the pieces make
    up the whole knowledge base, in order."""
    assert len(result.axioms) == result.accepted
    alone = [dl.parse_owl_functional_axioms(f"Ontology({a.text})") for a in result.axioms]
    assert all(r.accepted == 1 and r.ok and not r.consumed for r in alone)
    for axiom in result.axioms:
        assert result.functional_text[axiom.position:].startswith(axiom.text)
        assert axiom.text.startswith(axiom.keyword + "(")
    for holder in ("tbox", "abox"):
        whole = getattr(result, holder)
        for f in dataclasses.fields(whole):
            pieces = [getattr(getattr(r, holder), f.name) for r in alone]
            value = getattr(whole, f.name)
            assert (sum(pieces, []) if isinstance(value, list) else set().union(*pieces)) == value


@pytest.mark.parametrize("body, functional", [c[1:] for c in CASES], ids=[c[0] for c in CASES])
def test_each_construct_reads_as_its_functional_syntax(body, functional):
    reads_like(body, functional)


def test_the_cases_cover_reading_and_refusing():
    # A guard on the table itself: the oracle comparison above is only worth
    # something if it compares non-trivial results in both directions.
    accepted = refused = 0
    for _, body, _ in CASES:
        result = parse_owl_rdfxml(document(body))
        accepted += result.accepted
        refused += len(result.refused)
    # the eight cases from "one of" to "float literal"
    assert accepted >= 50 and refused == 8


def test_the_example_of_the_request():
    text = HEAD.replace('<!ENTITY ex "http://example.org/o#">',
                        '<!ENTITY obo "http://purl.obolibrary.org/obo/">') + """
<owl:Class rdf:about="&obo;ENVO_01000201">
    <owl:equivalentClass>
        <owl:Class>
            <owl:intersectionOf rdf:parseType="Collection">
                <rdf:Description rdf:about="&obo;ENVO_01001793"/>
                <owl:Restriction>
                    <owl:onProperty rdf:resource="&obo;RO_0000056"/>
                    <owl:someValuesFrom rdf:resource="&obo;ENVO_01001827"/>
                </owl:Restriction>
            </owl:intersectionOf>
        </owl:Class>
    </owl:equivalentClass>
    <rdfs:label>subtropical broadleaf forest biome</rdfs:label>
</owl:Class>
{declarations}
</rdf:RDF>
"""
    # ENVO declares the property and the classes; without the declarations the
    # restriction is not decided (an object or a data property?) and is refused.
    bare = parse_owl_rdfxml(text.replace("{declarations}", ""))
    assert bare.accepted == 0 and [r.keyword for r in bare.refused] == ["owl:onProperty"]
    assert "is not declared, and its filler is neither a class nor a data range" in bare.refused[0].reason
    result = parse_owl_rdfxml(text.replace("{declarations}", """
<owl:ObjectProperty rdf:about="&obo;RO_0000056"/>
<owl:Class rdf:about="&obo;ENVO_01001793"/>
<owl:Class rdf:about="&obo;ENVO_01001827"/>"""))
    assert result.functional_text == (
        "Ontology(\nEquivalentClasses(<ENVO_01000201> ObjectIntersectionOf(<ENVO_01001793> "
        "ObjectSomeValuesFrom(<RO_0000056> <ENVO_01001827>)))\n)\n")
    assert result.ok and result.accepted == 1 and result.annotations == 1
    assert result.iris["RO_0000056"] == "http://purl.obolibrary.org/obo/RO_0000056"
    (axiom,) = result.axioms
    # the axiom starts after "Ontology(" and its line break: 9 + 1 characters
    assert (axiom.keyword, axiom.subject, axiom.position) == ("EquivalentClasses", "ENVO_01000201", 10)
    assert axiom.text == ("EquivalentClasses(<ENVO_01000201> ObjectIntersectionOf(<ENVO_01001793> "
                          "ObjectSomeValuesFrom(<RO_0000056> <ENVO_01001827>)))")
    # A ≡ B ⊓ ∃p.C is the two inclusions A ⊑ B ⊓ ∃p.C and B ⊓ ∃p.C ⊑ A.
    assert result.to_kb().formula.to_unicode_str() == (
        "∀x (ENVO_01000201(x) → ENVO_01001793(x) ∧ ∃x0 (RO_0000056(x, x0) ∧ ENVO_01001827(x0))) ∧ "
        "∀x (ENVO_01001793(x) ∧ ∃x0 (RO_0000056(x, x0) ∧ ENVO_01001827(x0)) → ENVO_01000201(x))")


# --------------------------------------------------------------------------- #
# What the mapping itself refuses: by name, with the triples, never dropped.
# --------------------------------------------------------------------------- #

GOOD = '<owl:Class rdf:about="&ex;C"><rdfs:subClassOf rdf:resource="&ex;B"/></owl:Class>'


@pytest.mark.parametrize("body, keyword, reason, line", [
    ('<owl:Class rdf:about="&ex;A"><ex:undeclared rdf:resource="&ex;B"/></owl:Class>',
     EX + "undeclared", "neither OWL 2 vocabulary nor declared",
     f"<{EX}A> <{EX}undeclared> <{EX}B> ."),
    ('<rdf:Description rdf:about="&ex;a"><rdf:type rdf:resource="&ex;NotAClass"/></rdf:Description>',
     "rdf:type", "is not declared as a class", f"<{EX}a> <{RDF}type> <{EX}NotAClass> ."),
    ('<rdf:Description rdf:about="&ex;s"><rdfs:domain rdf:resource="&ex;A"/></rdf:Description>',
     "rdfs:domain", "not declared as an object, data or annotation property",
     f"<{EX}s> <{RDFS}domain> <{EX}A> ."),
    (sub_class(restriction("ex;s", card("minCardinality", 1))),
     "owl:onProperty", "whether it counts individuals or data values is not decided",
     f"<{OWL}onProperty> <{EX}s> ."),
    (sub_class('<owl:Class><owl:unionOf rdf:parseType="Collection"><rdf:Description rdf:about="&ex;B"/>'
               '</owl:unionOf></owl:Class>'),
     "owl:unionOf", "has 1 member(s), where OWL 2 has at least two", f"<{RDF}first> <{EX}B> ."),
    (sub_class(restriction("ex;p", '<owl:someValuesFrom rdf:resource="&ex;B"/>'
                                   '<owl:allValuesFrom rdf:resource="&ex;C"/>')),
     "owl:Restriction", "has 2 fillers", f"<{OWL}allValuesFrom> <{EX}C> ."),
    (sub_class(restriction("ex;p", '<owl:minCardinality>many</owl:minCardinality>')),
     "owl:minCardinality", "not a non-negative integer", '<' + OWL + 'minCardinality> "many" .'),
    (sub_class('<owl:Restriction><owl:onProperties rdf:parseType="Collection">'
               '<rdf:Description rdf:about="&ex;d"/><rdf:Description rdf:about="&ex;e"/>'
               '</owl:onProperties><owl:someValuesFrom rdf:resource="&xsd;integer"/></owl:Restriction>'),
     "owl:onProperties", "n-ary data restriction", f"<{OWL}onProperties>"),
    (sub_class('<owl:Class><owl:unionOf rdf:resource="&ex;B"/></owl:Class>'),
     "rdf:List", "is not a list of blank nodes ending in rdf:nil", f"<{OWL}unionOf> <{EX}B> ."),
    (restriction("ex;p", '<owl:someValuesFrom rdf:resource="&ex;B"/>'),
     "rdf:type", "part of no construct an OWL 2 axiom reads", f"<{OWL}someValuesFrom> <{EX}B> ."),
    ('<owl:DatatypeProperty rdf:about="&ex;p"/>'
     '<rdf:Description rdf:about="&ex;p"><rdfs:domain rdf:resource="&ex;A"/></rdf:Description>',
     "Declaration", "declared as data and as object property", f"<{EX}p> <{RDFS}domain> <{EX}A> ."),
    ('<rdf:Description rdf:about="&ex;s"><rdf:type rdf:resource="&owl;FunctionalProperty"/></rdf:Description>',
     "rdf:type", "not declared as an object or a data property",
     f"<{EX}s> <{RDF}type> <{OWL}FunctionalProperty> ."),
], ids=["undeclared predicate", "type of no class", "domain of no property",
        "cardinality on no property", "one-member union", "two fillers", "bad cardinality",
        "n-ary data restriction", "not a list", "unused restriction", "two kinds",
        "functional of no property"])
def test_the_mapping_refuses_by_name(body, keyword, reason, line):
    result = parse_owl_rdfxml(document(GOOD + body))
    mapping = [r for r in result.refused if r.position == -1]
    assert [r.keyword for r in mapping] == [keyword]
    assert reason in mapping[0].reason
    assert line in mapping[0].text
    # the rest of the document is read all the same
    assert result.accepted == 1 and result.tbox.inclusions[0] == (dl.Atomic("C"), dl.Atomic("B"))
    assert [a.text for a in result.axioms] == ["SubClassOf(<C> <B>)"]
    assert not result.ok


def test_a_refused_structure_is_reported_with_all_its_triples():
    unused = restriction("ex;p", '<owl:someValuesFrom rdf:resource="&ex;B"/>')
    (refusal,) = parse_owl_rdfxml(document(unused)).refused
    lines = refusal.text.split("\n")
    assert len(lines) == 3
    assert lines[0].endswith(f"<{RDF}type> <{OWL}Restriction> .")
    assert lines[1].endswith(f"<{OWL}onProperty> <{EX}p> .")
    assert lines[2].endswith(f"<{OWL}someValuesFrom> <{EX}B> .")


def test_one_declared_side_gives_the_other_its_kind():
    # 's' is declared nowhere; the only well-typed reading of p ⊑ s with p an
    # object property is an object property inclusion.
    reads_like('<rdf:Description rdf:about="&ex;p"><rdfs:subPropertyOf rdf:resource="&ex;s"/></rdf:Description>',
               "SubObjectPropertyOf(p s)")
    # a filler decides a restriction on an undeclared property
    reads_like(sub_class(restriction("ex;s", '<owl:someValuesFrom rdf:resource="&ex;B"/>')),
               "SubClassOf(A ObjectSomeValuesFrom(s B))")
    reads_like(sub_class(restriction("ex;t", '<owl:someValuesFrom rdf:resource="&xsd;integer"/>')),
               "SubClassOf(A DataSomeValuesFrom(t xsd:integer))")
    # a characteristic only object properties have makes an object property
    reads_like('<rdf:Description rdf:about="&ex;s"><rdf:type rdf:resource="&owl;TransitiveProperty"/>'
               '<rdfs:domain rdf:resource="&ex;A"/></rdf:Description>',
               "TransitiveObjectProperty(s) ObjectPropertyDomain(s A)")


def test_what_each_axiom_is_about():
    body = ('<owl:Class rdf:about="&ex;A"><rdfs:subClassOf rdf:resource="&ex;B"/></owl:Class>'
            '<owl:NamedIndividual rdf:about="&ex;a"><rdf:type rdf:resource="&ex;A"/>'
            '<ex:p rdf:resource="&ex;b"/></owl:NamedIndividual>'
            '<owl:AllDisjointClasses><owl:members rdf:parseType="Collection">'
            '<rdf:Description rdf:about="&ex;A"/><rdf:Description rdf:about="&ex;C"/>'
            '</owl:members></owl:AllDisjointClasses>'
            '<owl:Class><owl:unionOf rdf:parseType="Collection"><rdf:Description rdf:about="&ex;B"/>'
            '<rdf:Description rdf:about="&ex;C"/></owl:unionOf>'
            '<rdfs:subClassOf rdf:resource="&ex;A"/></owl:Class>'
            '<rdf:Description rdf:about="&ex;note"><rdfs:domain rdf:resource="&ex;A"/></rdf:Description>')
    result = parse_owl_rdfxml(document(body))
    assert [(a.keyword, a.subject) for a in result.axioms] == [
        ("SubClassOf", "A"), ("ClassAssertion", "a"), ("ObjectPropertyAssertion", "a"),
        ("DisjointClasses", None), ("SubClassOf", None)]
    # the annotation-property axiom is consumed, not accepted
    assert [c.keyword for c in result.consumed] == ["AnnotationPropertyDomain"]
    each_axiom_reads_alone(result)


def test_the_refusals_come_in_two_groups():
    body = (sub_class('<owl:Class><owl:oneOf rdf:parseType="Collection"><rdf:Description '
                      'rdf:about="&ex;a"/></owl:oneOf></owl:Class>')
            + '<owl:Class rdf:about="&ex;B"><ex:undeclared rdf:resource="&ex;C"/></owl:Class>')
    result = parse_owl_rdfxml(document(body))
    assert [(r.keyword, r.position >= 0) for r in result.refused] == \
        [("ObjectOneOf", True), (EX + "undeclared", False)]
    first = result.refused[0]
    assert result.functional_text[first.position:].startswith("ObjectOneOf")
    assert first.text == "SubClassOf(<A> ObjectOneOf(<a>))"


# --------------------------------------------------------------------------- #
# Annotations, deprecation, imports and the counts.
# --------------------------------------------------------------------------- #

def test_annotations_are_skipped_and_counted():
    body = """
<owl:Ontology rdf:about="http://example.org/o"><rdfs:comment>an ontology</rdfs:comment>
  <owl:versionIRI rdf:resource="http://example.org/o/1.0"/>
  <owl:imports rdf:resource="http://example.org/other"/></owl:Ontology>
<owl:Class rdf:about="&ex;A"><rdfs:label xml:lang="en">a</rdfs:label><ex:note>An A.</ex:note>
  <rdfs:subClassOf><owl:Restriction><owl:onProperty rdf:resource="&ex;p"/>
    <owl:someValuesFrom rdf:resource="&ex;B"/></owl:Restriction></rdfs:subClassOf></owl:Class>
<owl:Axiom><owl:annotatedSource rdf:resource="&ex;A"/><owl:annotatedProperty rdf:resource="&ex;note"/>
  <owl:annotatedTarget>An A.</owl:annotatedTarget><ex:remark>ref:1</ex:remark></owl:Axiom>
<owl:Axiom><owl:annotatedSource rdf:resource="&ex;A"/>
  <owl:annotatedProperty rdf:resource="http://www.w3.org/2000/01/rdf-schema#subClassOf"/>
  <owl:annotatedTarget><owl:Restriction><owl:onProperty rdf:resource="&ex;p"/>
    <owl:someValuesFrom rdf:resource="&ex;B"/></owl:Restriction></owl:annotatedTarget>
  <ex:remark>ref:2</ex:remark><rdfs:comment>checked</rdfs:comment></owl:Axiom>
<owl:Class rdf:about="&ex;B"><owl:deprecated rdf:datatype="&xsd;boolean">true</owl:deprecated></owl:Class>
"""
    result = parse_owl_rdfxml(document(body))
    # The copy of the restriction the second owl:Axiom points to is read with it.
    assert result.ok and result.accepted == 1
    assert result.tbox.inclusions == [(dl.Atomic("A"), dl.Exists("p", dl.Atomic("B")))]
    # ontology comment, label, note, deprecated: four assertions; ref:1, ref:2
    # and "checked" annotate reified axioms.
    assert result.annotations == 7
    # the vocabulary's declarations, then 4 annotation assertions
    assert result.skipped == VOCABULARY_DECLARATIONS + 4
    assert result.deprecated == ("B",)
    assert result.imports == ("http://example.org/other",)
    assert result.ontology_iri == "http://example.org/o"
    assert result.functional_text.startswith("Ontology(<http://example.org/o>\n")


def test_the_owl1_deprecated_class_declares_and_deprecates():
    result = parse_owl_rdfxml(document(
        '<owl:DeprecatedClass rdf:about="&ex;Old"/>'
        '<owl:Class rdf:about="&ex;Old"><rdfs:subClassOf rdf:resource="&ex;A"/></owl:Class>',
        vocabulary=False))
    assert result.ok and result.deprecated == ("Old",)
    # owl:DeprecatedClass is a declaration and a deprecation annotation; the
    # second node element repeats rdf:type owl:Class, a second declaration triple
    assert result.skipped == 3 and result.annotations == 1


def test_to_dict_carries_the_new_fields():
    result = parse_owl_rdfxml(document('<owl:Class rdf:about="&ex;Z"><rdfs:subClassOf rdf:resource="&ex;A"/>'
                                       '</owl:Class>'))
    as_dict = json.loads(json.dumps(result.to_dict()))
    assert as_dict["accepted"] == 1 and as_dict["iris"]["Z"] == EX + "Z"
    assert set(as_dict) >= {"annotations", "deprecated", "imports", "ontology_iri", "iris", "refused"}


# --------------------------------------------------------------------------- #
# Names.
# --------------------------------------------------------------------------- #

def test_local_names_and_their_iris():
    result = parse_owl_rdfxml(document('<owl:Class rdf:about="&ex;Z"><rdfs:subClassOf rdf:resource="&owl;Thing"/>'
                                       '</owl:Class>'))
    assert result.tbox.inclusions == [(dl.Atomic("Z"), dl.Top())]
    assert result.iris["Z"] == EX + "Z" and result.iris["owl:Thing"] == OWL + "Thing"
    # every declared entity is named, used in an axiom or not
    assert result.iris["note"] == EX + "note"


def test_a_shared_local_name_falls_back_to_the_full_iris():
    body = ('<owl:Class rdf:about="http://a.org/x#Dog"><rdfs:subClassOf rdf:resource="http://b.org/Dog"/>'
            '</owl:Class><owl:Class rdf:about="http://b.org/Dog"/>')
    result = parse_owl_rdfxml(document(body, vocabulary=False))
    assert result.tbox.inclusions == [(dl.Atomic("http://a.org/x#Dog"), dl.Atomic("http://b.org/Dog"))]
    assert set(result.iris) == {"http://a.org/x#Dog", "http://b.org/Dog"}


@pytest.mark.parametrize("iri, name", [
    ("http://example.org/o#a:b", "http://example.org/o#a:b"),     # a ':' in the local name
    ("http://example.org/o/", "http://example.org/o/"),           # empty local name
    ("urn:isbn:0451450523", "urn:isbn:0451450523"),               # no '/' or '#'
    ("http://example.org/o/Plain", "Plain"),
])
def test_when_the_local_name_is_not_used(iri, name):
    result = parse_owl_rdfxml(document(f'<owl:Class rdf:about="{iri}"><rdfs:subClassOf rdf:resource="&ex;A"/>'
                                       f'</owl:Class>'))
    assert result.tbox.inclusions == [(dl.Atomic(name), dl.Atomic("A"))]
    assert result.iris[name] == iri


def test_full_iri_names():
    result = parse_owl_rdfxml(document(GOOD), names="iri")
    assert result.tbox.inclusions == [(dl.Atomic(EX + "C"), dl.Atomic(EX + "B"))]
    assert all(name == iri for name, iri in result.iris.items() if ":" not in name[:5])
    with pytest.raises(ValueError, match="names must be"):
        parse_owl_rdfxml(document(GOOD), names="short")


def test_the_names_map_is_one_to_one():
    body = ('<owl:Class rdf:about="http://a.org/x#Dog"/><owl:Class rdf:about="http://b.org/Dog"/>'
            '<owl:Class rdf:about="http://b.org/Cat"><rdfs:subClassOf rdf:resource="http://a.org/x#Dog"/></owl:Class>')
    iris = parse_owl_rdfxml(document(body)).iris
    assert len(set(iris.values())) == len(iris)


# --------------------------------------------------------------------------- #
# Sources and bases.
# --------------------------------------------------------------------------- #

def test_a_path_text_or_bytes(tmp_path):
    text = document(GOOD)
    path = tmp_path / "o.owl"
    path.write_text(text, encoding="utf-8")
    results = [parse_owl_rdfxml(source) for source in (text, text.encode("utf-8"), path, str(path))]
    assert all(r.tbox == results[0].tbox and r.accepted == 1 for r in results)


def test_relative_iris_resolve_against_the_file_or_the_base(tmp_path):
    body = '<owl:Class rdf:about="Z"><rdfs:subClassOf rdf:resource="Y"/></owl:Class>'
    path = tmp_path / "o.owl"
    path.write_text(document(body, vocabulary=False), encoding="utf-8")
    from_file = parse_owl_rdfxml(path)
    assert from_file.iris["Z"] == path.resolve().as_uri()[:-len("o.owl")] + "Z"
    given = parse_owl_rdfxml(path, base="http://example.org/dir/doc")
    assert given.iris["Z"] == "http://example.org/dir/Z"
    # text without a base keeps a relative IRI as it is written
    assert parse_owl_rdfxml(document(body, vocabulary=False)).iris["Z"] == "Z"


# --------------------------------------------------------------------------- #
# Step 1: the RDF/XML grammar.
# --------------------------------------------------------------------------- #

def _signatures(triples):
    """A multiset of the triples with each blank node replaced by its structure
    (the blank nodes here form trees, for which equal multisets mean isomorphic
    graphs)."""
    out = collections.defaultdict(list)
    for s, p, o in triples:
        out[s].append((p, o))

    def sig(term):
        if isinstance(term, str) and term.startswith("_:"):
            return ("_", tuple(sorted((p, sig(o)) for p, o in out[term])))
        return term

    return collections.Counter((sig(s), p, sig(o)) for s, p, o in triples)


GRAMMAR_BASE = """<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:ex="http://example.org/o#" xml:base="http://example.org/base/doc">
{}
</rdf:RDF>"""
B = "http://example.org/base/"

GRAMMAR = [
    ("typed node, property attributes, xml:lang",
     '<ex:Dog rdf:about="rex" ex:name="Rex" xml:lang="en" rdf:type="http://example.org/o#Pet"/>',
     [(B + "rex", RDF + "type", EX + "Dog"), (B + "rex", EX + "name", _Literal("Rex", None, "en")),
      (B + "rex", RDF + "type", EX + "Pet")]),
    ("rdf:ID, rdf:nodeID, nested xml:base",
     '<rdf:Description rdf:ID="a"><ex:knows rdf:nodeID="n1"/>'
     '<ex:sees xml:base="http://other.org/dir/" rdf:resource="x"/></rdf:Description>'
     '<rdf:Description rdf:nodeID="n1"><ex:name>N</ex:name></rdf:Description>',
     [(B + "doc#a", EX + "knows", "_:1"), (B + "doc#a", EX + "sees", "http://other.org/dir/x"),
      ("_:1", EX + "name", _Literal("N"))]),
    ("parse types, rdf:li, datatype, empty elements",
     '<rdf:Description rdf:about="http://example.org/s">'
     '<ex:addr rdf:parseType="Resource"><ex:city>Osnabrück</ex:city></ex:addr>'
     '<ex:items rdf:parseType="Collection"><rdf:Description rdf:about="http://example.org/i1"/>'
     '<rdf:Description rdf:about="http://example.org/i2"/></ex:items>'
     '<ex:none rdf:parseType="Collection"/>'
     '<ex:age rdf:datatype="http://www.w3.org/2001/XMLSchema#integer">42</ex:age>'
     '<ex:empty/><ex:made ex:by="Ann"/><rdf:li>first</rdf:li><rdf:li>second</rdf:li>'
     '</rdf:Description>',
     [("http://example.org/s", EX + "addr", "_:1"), ("_:1", EX + "city", _Literal("Osnabrück")),
      ("http://example.org/s", EX + "items", "_:2"), ("_:2", RDF + "first", "http://example.org/i1"),
      ("_:2", RDF + "rest", "_:3"), ("_:3", RDF + "first", "http://example.org/i2"),
      ("_:3", RDF + "rest", RDF + "nil"), ("http://example.org/s", EX + "none", RDF + "nil"),
      ("http://example.org/s", EX + "age", _Literal("42", XSD + "integer")),
      ("http://example.org/s", EX + "empty", _Literal("")),
      ("http://example.org/s", EX + "made", "_:4"), ("_:4", EX + "by", _Literal("Ann")),
      ("http://example.org/s", RDF + "_1", _Literal("first")),
      ("http://example.org/s", RDF + "_2", _Literal("second"))]),
    ("reification by rdf:ID on a property element",
     '<rdf:Description rdf:about="http://example.org/s"><ex:p rdf:ID="st" rdf:resource="http://example.org/v"/>'
     '</rdf:Description>',
     [("http://example.org/s", EX + "p", "http://example.org/v"),
      (B + "doc#st", RDF + "type", RDF + "Statement"), (B + "doc#st", RDF + "subject", "http://example.org/s"),
      (B + "doc#st", RDF + "predicate", EX + "p"), (B + "doc#st", RDF + "object", "http://example.org/v")]),
]


@pytest.mark.parametrize("body, expected", [g[1:] for g in GRAMMAR], ids=[g[0] for g in GRAMMAR])
def test_the_rdfxml_grammar(body, expected):
    assert _signatures(_read_triples(GRAMMAR_BASE.format(body))) == _signatures(expected)


def test_an_xml_literal():
    (triple,) = _read_triples(GRAMMAR_BASE.format(
        '<rdf:Description rdf:about="http://example.org/s"><ex:note rdf:parseType="Literal">'
        '<b xmlns="http://www.w3.org/1999/xhtml">bold</b> text</ex:note></rdf:Description>'))
    assert triple[2].datatype == RDF + "XMLLiteral"
    assert "bold</" in triple[2].lexical and triple[2].lexical.endswith(" text")


def test_dtd_entities_are_expanded():
    triples = _read_triples(document('<owl:Class rdf:about="&ex;Z"/>', vocabulary=False))
    assert triples == [(EX + "Z", RDF + "type", OWL + "Class")]


def test_a_node_element_is_a_document_of_its_own():
    text = (f'<ex:Dog xmlns:ex="{EX}" xmlns:rdf="{RDF}" rdf:about="http://example.org/rex">'
            '<ex:name>Rex</ex:name></ex:Dog>')
    assert _read_triples(text) == [("http://example.org/rex", RDF + "type", EX + "Dog"),
                                   ("http://example.org/rex", EX + "name", _Literal("Rex"))]


def test_a_document_longer_than_one_read_is_read_whole(tmp_path):
    """The document is fed to the parser 64 KiB at a time. The comment in front
    is as long as it takes for the two bytes of a ``ü`` to fall on both sides of
    the first boundary; node elements fall across every boundary anyway."""
    body = "".join(f'<owl:Class rdf:about="&ex;K{i}"><rdfs:label>Osnabrück</rdfs:label></owl:Class>'
                   for i in range(3000))

    def padded(n):
        return document("<!--" + "x" * n + "-->" + body, vocabulary=False)

    umlaut = "ü".encode("utf-8")
    first = max(m.start() for m in re.finditer(umlaut, padded(0).encode("utf-8"))
                if m.start() <= 65535)
    text = padded(65535 - first)
    assert text.encode("utf-8")[65535:65537] == umlaut
    expected = []
    for i in range(3000):
        expected += [(f"{EX}K{i}", RDF + "type", OWL + "Class"),
                     (f"{EX}K{i}", RDFS + "label", _Literal("Osnabrück"))]
    path = tmp_path / "o.owl"
    path.write_bytes(text.encode("utf-8"))
    for source in (text, text.encode("utf-8"), path):
        assert _read_triples(source) == expected


def test_a_node_element_is_dropped_once_it_is_read():
    """At most three node elements are in the tree at any event: the one read
    last (its tail is still unknown), the one being read and the start of the
    next, when one piece of input holds both."""
    text = GRAMMAR_BASE.format("".join(f'<rdf:Description rdf:about="http://example.org/s{i}"/>'
                                       for i in range(20)))
    sizes = []

    def watched(events):
        root = None
        for event, elem in events:
            root = elem if root is None else root
            sizes.append(len(root))
            yield event, elem

    reader = _TripleReader()
    reader.document(watched(_events(text[i:i + 16] for i in range(0, len(text), 16))), "")
    assert len(reader.triples) == 0 and max(sizes) <= 3
    # read in one piece, the parser has built the whole tree before the first event
    reader.document(watched(_events([text])), "")
    assert max(sizes) == 20


@pytest.mark.parametrize("body", [
    'text<rdf:Description rdf:about="http://example.org/s"/>',
    '<rdf:Description rdf:about="http://example.org/s"/>text<rdf:Description rdf:about="http://example.org/t"/>',
    '<rdf:Description rdf:about="http://example.org/s"/>text',
    "text",
], ids=["before the first node element", "between two", "after the last", "with none"])
def test_text_directly_inside_rdf_rdf_raises(body):
    with pytest.raises(OwlRdfXmlSyntaxError, match="text directly inside rdf:RDF"):
        _read_triples(GRAMMAR_BASE.format(body))


@pytest.mark.parametrize("text, message", [
    ("<rdf:RDF", "not well-formed XML"),
    ('<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"><Thing/></rdf:RDF>', "no namespace"),
    (GRAMMAR_BASE.format('<rdf:Description rdf:about="http://example.org/s"><ex:p>'
                         '<rdf:Description/><rdf:Description/></ex:p></rdf:Description>'),
     "more than one node element"),
    (GRAMMAR_BASE.format('<rdf:Description rdf:about="http://example.org/s">text</rdf:Description>'),
     "where only property elements belong"),
    (GRAMMAR_BASE.format('<rdf:Description rdf:about="http://example.org/s" rdf:nodeID="x"/>'),
     "more than one of rdf:about, rdf:ID and rdf:nodeID"),
])
def test_what_is_not_rdfxml_raises(text, message):
    with pytest.raises(OwlRdfXmlSyntaxError, match=message):
        parse_owl_rdfxml(text)


def test_rdflib_reads_the_same_triples(monkeypatch):
    rdflib = pytest.importorskip("rdflib")
    monkeypatch.setattr(rdflib, "NORMALIZE_LITERALS", False)

    def ours(term):
        if isinstance(term, _Literal):
            return ("L", term.lexical, term.datatype or "", (term.language or "").lower())
        return term

    def theirs(term):
        if isinstance(term, rdflib.Literal):
            return ("L", str(term), str(term.datatype or ""), (term.language or "").lower())
        if isinstance(term, rdflib.BNode):
            return "_:" + str(term)
        return str(term)

    documents = [GRAMMAR_BASE.format(g[1]) for g in GRAMMAR] + [document(c[1]) for c in CASES]
    for text in documents:
        graph = rdflib.Graph().parse(data=text, format="xml")
        assert _signatures([tuple(ours(t) for t in triple) for triple in set(_read_triples(text))]) == \
            _signatures([tuple(theirs(t) for t in triple) for triple in graph])


# RFC 3986, section 5.4: the base and every normal and abnormal example.
RFC_BASE = "http://a/b/c/d;p?q"
RFC_EXAMPLES = {
    "g:h": "g:h", "g": "http://a/b/c/g", "./g": "http://a/b/c/g", "g/": "http://a/b/c/g/",
    "/g": "http://a/g", "//g": "http://g", "?y": "http://a/b/c/d;p?y", "g?y": "http://a/b/c/g?y",
    "#s": "http://a/b/c/d;p?q#s", "g#s": "http://a/b/c/g#s", "g?y#s": "http://a/b/c/g?y#s",
    ";x": "http://a/b/c/;x", "g;x": "http://a/b/c/g;x", "g;x?y#s": "http://a/b/c/g;x?y#s",
    "": "http://a/b/c/d;p?q", ".": "http://a/b/c/", "./": "http://a/b/c/", "..": "http://a/b/",
    "../": "http://a/b/", "../g": "http://a/b/g", "../..": "http://a/", "../../": "http://a/",
    "../../g": "http://a/g",
    "../../../g": "http://a/g", "../../../../g": "http://a/g", "/./g": "http://a/g",
    "/../g": "http://a/g", "g.": "http://a/b/c/g.", ".g": "http://a/b/c/.g",
    "g..": "http://a/b/c/g..", "..g": "http://a/b/c/..g", "./../g": "http://a/b/g",
    "./g/.": "http://a/b/c/g/", "g/./h": "http://a/b/c/g/h", "g/../h": "http://a/b/c/h",
    "g;x=1/./y": "http://a/b/c/g;x=1/y", "g;x=1/../y": "http://a/b/c/y",
    "g?y/./x": "http://a/b/c/g?y/./x", "g?y/../x": "http://a/b/c/g?y/../x",
    "g#s/./x": "http://a/b/c/g#s/./x", "g#s/../x": "http://a/b/c/g#s/../x", "http:g": "http:g",
}


@pytest.mark.parametrize("ref, target", sorted(RFC_EXAMPLES.items()))
def test_rfc3986_resolution(ref, target):
    assert _resolve(RFC_BASE, ref) == target


def test_an_absolute_iri_loses_its_dot_segments():
    assert _resolve("", "http://a/b/../c/./d") == "http://a/c/d"
    assert _resolve("", "http://purl.obolibrary.org/obo/ENVO_1") == "http://purl.obolibrary.org/obo/ENVO_1"
