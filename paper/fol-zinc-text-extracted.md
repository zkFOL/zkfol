# Text extracted from `fol-zinc.pdf`

This file is generated from the supplied PDF. It is included for quick text search and orientation only; the authoritative paper file is `fol-zinc.pdf`.

```text
Integer SNARKs for First-Order Logic

Murdoch J. Gabbay
ORCID: https://orcid.org/0000-0001-5796-3455
Heriot-Watt University, Edinburgh, United Kingdom

Andrew Mendelsohn
ORCID: https://orcid.org/0000-0003-4735-7157
Imperial College London, London, United Kingdom


Abstract

We efficiently arithmetise first-order logic (FOL) to SNARK-friendly relations. FOL is a highly
expressive and widely-used mathematical logic capable (amongst other things) of expressing
Turing-complete computational systems. We provide a framework for arithmetising FOL by extending a
univariate polynomial semantics for FOL proposed by the first author (J. of Applied Logics ’25) to a
general semantics parameterised by a chosen tuple of functions satisfying some compatibility
properties. We instantiate this framework with multilinear polynomials having integer coefficients,
for their cryptographic utility. Validity judgements in the resulting semantics amount to a
combination of range checks and polynomial constraints on the inputs, which fit tidily into the
algebraic indexed relations of Zinc (Crypto ’25). By compiling a suitable polynomial interactive
oracle proof with the polynomial commitment scheme ‘Zip’ (cf. Zinc), we obtain a SNARK for relations
expressed in FOL. Our arithmetisation runs over the integers, obviating the need for a (costly)
final step of converting the initial relations into finite field-based relations.

This draft was compiled for inclusion in the zkFOL implementation repository on 29th September 2026.

2012 ACM Subject Classification

Theory of computation → Interactive proof systems; Theory of computation → Cryptographic protocols;
Security and privacy → Privacy-preserving protocols; Theory of computation → Logic and verification;
Mathematics of computing → Probabilistic algorithms; Security and privacy → Information-theoretic
techniques

Keywords and phrases

first-order logic, SNARKs, cryptographic proofs, arithmetisation

Digital Object Identifier

10.4230/LIPIcs.CVIT.2016.23

Acknowledgements

The authors would like to thank Albert Garreta and Alberto Centelles for helpful discussions.


© Murdoch Jamie Gabbay and Andrew Mendelsohn;
licensed under Creative Commons License CC-BY 4.0
42nd Conference on Very Important Topics (CVIT 2016).
Editors: John Q. Open and Joan R. Access; Article No. 23; pp. 23:1–23:25
Leibniz International Proceedings in Informatics
Schloss Dagstuhl – Leibniz-Zentrum für Informatik, Dagstuhl Publishing, Germany


1  Introduction

We give a compositional arithmetisation of first-order logic (FOL) to SNARK-friendly relations,
using Zinc [18]. The slogan is: cryptographic certificates of first-order validity over finite
models.

Our FOL arithmetisation generalises a prior univariate polynomial semantics [15] to a generic
sound-and-complete semantics parameterised by tuples of functions (ℱ in the mathematics below)
satisfying some compatibility properties. We then instantiate this semantics with integer
multilinear polynomials. This bridges from range-checked FOL validity over finite models, to
polynomial constraints compatible with Zinc. Logical instance-witness pairs transform via this
bridge to instance-witness pairs of a Zinc-compatible SNARK. We now explain FOL, SNARKs, and Zinc,
and how they fit together.


FOL

First-order logic is a powerful mathematical logic [4, 13] which more than suffices to specify
computation (including Turing-complete computation) and correctness properties thereof. The
following statements are all expressible in FOL: “Function f computes the square root” or “Abstract
machine A, when given input x, returns output f(x)” or “Transaction t is valid according to the
rules of the system” or “Proposed state-change S is compliant with legal requirement Z”, etc. FOL is
a quantified logic, with notions of universal and existential quantification: these can be expressed
with the familiar symbols ∀x.ϕ(x) and ∃x.ϕ(x).

FOL comes with a well-studied and simple sets-based notion of model: we assume a set X of elements
and we interpret universal quantification as quantification over elements in X; existential
quantification as existence of some element in X; and we interpret an n-ary relation R as a subset
of X^n; and so on. The FOL notion of truth is simple too: a predicate is just true or false of a
model, and notions of logical conjunction, disjunction, and negation are the usual Boolean
operations. [fn 1]

The above properties mean we can use FOL to simply and cleanly specify finite logical and
computational behaviour and to state correctness properties of that behaviour. [fn 2] FOL, therefore,
has a particularly useful application in formal verification.

However, FOL has no native cryptographic content: its intrinsic truth-theoretic notions of universal
and existential quantification, ∀x.ϕ(x) and ∃x.ϕ(x), for example, simply mean ‘check ϕ(x) for every
x’ and ‘check possible x until we find one such that ϕ(x)’.


SNARKs

A SNARK is a cryptographic tool to allow a prover to convince a verifier that the prover knows a
witness w such that (x, w) ∈ ℛ for some relation ℛ and instance x, succinctly (i.e. requiring
minimal work from the verifier), and in zero knowledge (i.e. the verifier does not learn information
about the witness w). [fn 3]

Most SNARKs work over a fixed finite field, determined by some prime power q = p^r (e.g. [20, 16,
12]). Using finite field arithmetic allows instance-witness pairs in NP relations to be efficiently
and succinctly checked for validity. A common three-step modular framework has been developed for
constructing SNARKs:

1. Build a polynomial interactive oracle proof (PIOP).
2. Build a polynomial commitment scheme (PCS).
3. Compile the PIOP+PCS to a SNARK via the transform of [6, 8].

The PIOP is an information theoretic component, and the PCS provides cryptographic guarantees of the
security of the construction.


The wrinkle.

A common problem in the real-world use of SNARKs is that we often want to prove things that are not
naturally expressed by relations ℛ defined by means of arithmetic over finite fields, much less by
arithmetic over a single fixed finite field.

To compensate, a so-called arithmetisation pre-processing step is required, which transforms the
relation ℛ of instance-witness pairs about which we actually want to prove knowledge, into some
suitably equivalent ‘SNARK friendly’ relation ℛ′, which is over a finite field and thus more
amenable to the technical requirements of SNARKs.

The SNARK friendly ℛ′ is typically defined by a polynomial expression, which may then be rewritten
to an even more SNARK friendly instance of a constraint system, such as R1CS or CCS [27]. We then
run the SNARK on the resulting system of constraints.

For instance: we may want to prove knowledge of the result of a computation which was performed over
the rationals ℚ (which is not a finite field), or over a ring which is not a field, such as ℤ/nℤ for
composite n. Converting these ‘natural’ relations and constraints determined by such computations
into constraints over finite fields can be computationally expensive to perform, as well as causing
a significant increase in the instance size upon which a SNARK is run, resulting in a costlier
proof. This motivates the study of techniques to avoid or reduce the burden of arithmetisation
overheads.


Zinc

Zinc [18] attempts to ameliorate the cost of arithmetisation. It does not make it go away, but it
pushes development effort away from the programmer and onto the cryptographic back-end. In
particular, Zinc gives a PIOP for relations defined over the integers ℤ, together with a PCS dubbed
‘Zip’, which compile to yield a SNARK.

Zinc allows for succinct proofs of relations with mixed characteristic, over numerous rings, to be
provided by a prover. The central concept of Zinc is quite simple: for well-chosen parameters, we
just sample some random primes (up to some bound) and run a finite field SNARK on the relation
instances modulo the sampled primes, with low resulting soundness error. This removes the need to
arithmetise such instances, beyond modular reduction. We note the relations in Zinc are defined on
multilinear polynomials with integer coefficients.


Full circle back to FOL

Previous work [15] shows how to translate FOL to (high degree, univariate) polynomials with integer
coefficients, such that the standard FOL truth-table-and-sets-based notion of validity may be
soundly and completely expressed using polynomial root tests: that is, a certain polynomial ⟨ϕ⟩
corresponding to the predicate ϕ has roots over a certain set if and only if that predicate is true
in its standard FOL semantics. However, [15] did not attempt to connect the resulting integer
polynomials to a cryptographic backend.

In this work, therefore, we provide such a bridge to a cryptographic backend. We replace the high
degree univariate FOL semantics of [15] with a multivariate semantics, instantiating the general
semantics referred to in the first paragraph of this introduction with a set ℱ of multilinear
interpolating polynomials of integer witness vectors. While we could choose any set of functions
satisfying the necessary compatibility properties for our general semantics, not only functions that
are interpolant polynomials, we choose multilinear polynomials with integer coefficients, popular
for their cryptographic utility in building PCS [30], for compatibility with Zinc. Validity
judgements in the resulting semantics (Definition 20) then amount to a combination of range checks
and polynomial constraints on the inputs (Corollary 28) which fit into the algebraic indexed
relations of [18].

Via the polynomial interactive oracle proof (PIOP) plus polynomial commitment scheme (PCS) framework
[6, 8], from any compatible PIOP and Zip [18, Section 5] we obtain a SNARK for statements expressed
in FOL (Corollary 32). Our reliance on Zinc ensures that the verifier complexity of our construction
is desirably low, and since Zinc is a hash-based SNARK, our construction is plausibly post-quantum
secure.


1.1  Contributions

We now provide an overview of our contributions in more detail. We omit the technical details of
range-checks on the various data, so that we can focus on the core ideas of the construction. We
begin with a model of FOL in which we can write logical predicates; predicate here simply means a
logical statement about an object, which can be evaluated to true or false. After defining our model
of FOL, we give a semantics for FOL over the integers. This means that, at a high level, we design

1. a map (in our jargon, an interpretation) from the symbols comprising our model of FOL to the
   integers, and
2. rules for evaluating the logical veracity of FOL predicates by manipulating the integers obtained
   under this map (in the jargon, we can ‘evaluate validity judgments’).

The achievement of Section 2 is to design such rules which are sound and complete: this simply means
the predicates are true (or false) if and only if the integer manipulations evaluate to zero (or
non-zero). Our rules for integer manipulation are simple: logical equality of terms t =̲ t′ is
mapped to the square of the difference of the interpretations of t and t′; logical conjunction t ∧̲
t′ (read: t AND t′) is mapped to the sum of the interpretations of t and t′; and logical disjunction
t ∨̲ t′ (read: t OR t′) is mapped to the product of the interpretations of t and t′. We emphasise
for the benefit of the reader that what is termed an ‘interpretation’ is just a map from terms to
integers. The rules are defined in Figure 2 and the proof of soundness and completeness given in
Theorem 19.

At this point it is necessary to provide some detail about our FOL model. We define a flavour of FOL
using a novel concept we name enriched polynomials. To explain what these are, we introduce symbols
named matrix variable symbols, which are pairs (C, ar(C)) consisting of a variable symbol C and an
associated integer ar(C) ∈ ℕ (in our jargon, the ‘arity’ of C). This associated integer should be
thought of (with little harm done) as the number of ‘rows’ of the corresponding matrix variable
symbol. We write the ith ‘row’ of C as C_i. We define the aforementioned interpretations of matrix
variable symbols, written ς(C), as a matrix of integers with ith row ς(C_i) = ς(C)_i. Enriched
polynomials then are a combination of (in this paper) two or three purely formal symbols C_i, C_j,
and X, suggestively presented as

    C_i(X)    or    C_i C_j(X)

C_i(X) reminds us of actual polynomials, and C_i C_j(X) reminds us of composition of polynomials. We
introduce these symbolic ‘polynomials’ because we can in fact map them to actual polynomials. To do
this, we introduce a final set of variable symbols: these are symbols B_{i,ν}^{j,x} with four
indices i, j, x, ν ∈ ℕ. Here ν ∈ [maxbl] for some integer maxbl ∈ ℕ. We denote these by ‘B’ because
each such symbol will correspond to a bit in the binary decomposition of an integer entry of ς(C).
Again, we emphasise that these are just formal symbols.

To obtain polynomials we define a map inductively (see Figure 4) from enriched polynomials to
multilinear polynomials over the integers. We make use of the standard polynomial which sends a
string of binary digits to its corresponding integer. We denote this binary-to-integer polynomial by
b2int(X_1, ..., X_n). Our inductive map is then defined by

    C_i(X) ↦ b2int(B_{i,1}^{0,x}, ..., B_{i,maxbl}^{0,x}),
    C_i C_j(X) ↦ b2int(B_{i,1}^{j,x}, ..., B_{i,maxbl}^{j,x}),

extended homomorphically over sums and products. Thus we can take any FOL predicate ϕ expressed in
our symbolic notation of enriched polynomials, and transform it under this map to obtain actual
multivariate polynomials, constructed as sums and products of polynomials in the B_{i,ν}^{j,x}
symbols. We may of course evaluate these polynomials, simply by replacing the B_{i,ν}^{j,x} symbols
with bits of our choice and computing the evaluation as is done for more familiar kinds of
polynomials.

The achievement of Section 3 is to prove the following remarkable property of the resulting
multivariate polynomials: suppose we have a FOL predicate ϕ, defined using matrix variable symbol C,
transformed to a multivariate polynomial as above using an interpretation ς, and suppose ς(C) has ℓ
columns. Define the set of functions ℱ = {f_i = (x∈[ℓ] ↦ ς(C)@_{i,x}) | i ∈ [ar(C)]}, where
ς(C)@_{i,x} is the i, xth entry of the integer matrix ς(C). Then, if we replace

    B_{i,ν}^{0,x} with π_ν ∅_b f_i(x),    and    B_{i,ν}^{j,x} with π_ν ∅_b f_i(f_j(x)),

where ∅_b(x) is the integer-to-binary-decomposition map sending x ∈ ℕ to a vector of bits satisfying
b2int(∅_b(x)) = x, and π_ν(v) is the projection onto the νth entry of the vector v, then the
evaluation of our multivariate polynomials at these specified bits is in fact identical to the
logical evaluation of ϕ. [fn 4] That is to say, our multivariate polynomials evaluate at the
specified bits to zero if and only if the FOL predicate ϕ is true (see Corollary 28).

This is the fact that will allow us to produce a SNARK for FOL in Section 4. The flow of the SNARK
construction is as follows: we take a FOL predicate ϕ, generate the corresponding multivariate
polynomials, denoted mkQ_ℱ^x(⟨ϕ⟩) and parameterised over x ∈ [ℓ], and set them to be a collection of
public constraints.

Morally, the witness is the interpretation ς(C). However, in order to make use of efficient
polynomial commitment schemes, we compute the multilinear extensions of the rows of ς(C). This
collection of polynomials takes the place of the functions {f_i | i ∈ [ar(C)]} above. We then set
the witness to be the vector of multilinear extension polynomials of the rows of ς(C):

    𝐰 = (f_1, ..., f_{ar(C)})

Continuing with the the setup of our SNARK, polynomial commitments to these multilinear extensions
are computed using Zip [18] and then published along with the instance data.


Footnotes

[fn 1] Some shibboleths exist about FOL. “Over finite structures, NP is equal to the set of
        properties expressible in existential second-order logic (ESO), so FOL could not possibly
        express computation.” This is a category error. NP=ESO is a result in descriptive
        complexity, concerning properties of finite input structures defined by a fixed logical
        sentence; our use of FOL here is as a specification language whose models encode entire
        computations. “FOL is undecidable, so it cannot be used to do any actual reasoning.” This
        refers to the fact that no algorithm exists which, given an arbitrary FOL sentence ϕ, checks
        whether ϕ is valid in all structures. The undecidability reflects the fact that FOL theories
        can encode unbounded computation. However, we can check validity of a first-order formula
        over a particular finite structure by direct evaluation, since all quantification is over a
        finite domain.

[fn 2] Actually, FOL is a family of logics: there is FOL with equality, FOL with function-symbols,
        FOL with reification, FOL with pattern-matching, and so on. We see no inherent barriers to
        adapting the FOL language of this paper with extra bells and whistles.

[fn 3] The abstract logical content here is minimal: the relation ℛ under consideration is
        arbitrary. The focus here is on the cryptographic content. Even at this point, the reader
        can see where we are heading: we will marry the logical expressivity of FOL with the
        cryptographic efficiency of SNARKs, using Zinc.

[fn 4] As long as the composition f_i(f_j(x)) is well-defined.

We make the mild stipulation that the outputs of the PCS commitments are represented in binary, so
that composition of the multilinear extensions polynomials is well-defined. [fn 5] To guarantee the
prover’s PCS responses are supplying binary values to the verifier, we also append to the set of
instance constraints polynomials of the form

                         B_{i,ν}^{j,x}(B_{i,ν}^{j,x} − 1)

The instance constraints, polynomial commitments, and witness data are then integrated into the PIOP
of Zinc, from which the SNARK is compiled and run.

We can then prove, in zero-knowledge, knowledge of tuples of binary values on which each
mkQ_ℱ^x(⟨ϕ⟩) evaluates to zero. From the foregoing exposition, these mkQ_ℱ^x multivariate
polynomials all evaluate to zero if and only if ϕ is valid, thereby proving knowledge of a witness
for a logical instance. The resulting SNARK is analysed in Corollary 32.

A prototype (human-written) implementation of the core building blocks of our arithmetisation is at
https://anonymous.4open.science/r/zk-SNARKs-for-First-Order-Logic-2A41. This provides a
proof-of-concept, not an optimised implementation. Optimised, performant code is in active
development.


Examples

We showcase our work with regards to two simple examples of computation in Appendix D:
exponentiation and SK combinator reduction.

We include exponentiation to illustrate that we can consider mathematical functions in our
framework. It should be clear that other, more elaborate functions would just require writing other,
more elaborate FOL definitions.

On the other hand, SK combinators form a powerful and mathematically convenient Turing-complete
computational model. Haskell can be compiled to SK combinators directly [fn 6] [3] and only slightly
more complex combinatory systems are used as practical compilation targets for industrial
programming languages (a clean example is Nock [29]). Combinators admit a particularly compact
expression in FOL, so the import of both examples is that we can arithmetise logical assertions (by
definition; FOL is a logic), functions, and programs, covering (albeit in toy form) all the major
food groups of logic and computation, so to speak.


Related work

Other recent works have sought to address the problems of arithmetisation. Prior to Zinc, [9, 10]
aimed to build a SNARK for integer relations. However, they relied on the so-called Hidden Order
Groups assumption, which does not provide post-quantum security. There are also ‘field-agnostic’
SNARKs, which can prove validity of instances of relations defined over any finite field [19, 27, 7,
33]. However, these schemes could not handle the setting of infinite fields or integral domains
which are not fields. There are also schemes targeting relations over finite rings which are not
fields, e.g. [17, 31, 32]. In a different direction, [21, 2] designed tools (‘Distiller’, ‘Reef’)
which reduce the number of constraints required to provide a proof of an original computation. Such
methods could be used concurrently with our work here. Similarly [25] is concerned with reducing the
amount of ‘foreign field’ arithmetic required in proof systems. Akin to our application to SK
combinators, [5, 26] design SNARKs targeting computations performed in a specific programming
language, in their case in C. See [22, 24] for an introduction to SNARKs.

[fn 5] For f_i ∘ f_j(x) to be well-defined, where f_i and f_j are multilinear extensions, we only
        require the PCS responses for queries to the commitment to f_j be returned in binary form.
        This observation reduces the number of variables required in our constraints and leads to a
        significant performance improvement.

[fn 6] The compilation in [3] is to SKI, but the I combinator can be expressed using S and K.


Paper structure

Figure 1 gives a FOL syntax. Figure 3 gives an integer semantics ⟨·⟩_ς^x. Terms evaluate to possibly
negative integers, but predicates and range checks evaluate to natural numbers (Lemma 17). The
integer semantics is sound and complete by Theorem 19. We then consider a chain of compilations: a
compilation ⟨·⟩ of FOL syntax to enriched polynomials (Figure 2); a compilation mkQ_ℱ^x of enriched
polynomials to multivariate polynomials (Figure 4); and an evaluation from multivariate polynomials
to integers (Definition 25). Equivalence of this sequence of compilations with the integer semantics
is our main technical result (Theorem 27). By Corollary 28, FOL validity is equivalent to a relation
determined by polynomial equalities, so that we obtain a SNARK for FOL in Section 4.


2  Polynomials, SNARKs, FOL

Basic definitions

We begin with some notation:

▶ Notation 1. (i) ℤ = {…, −1, 0, 1, …} is the integers and ℕ = {0, 1, 2, …} is the non-negative
  integers and ℚ is the rational numbers. Given n ∈ ℕ write [n] for {1, …, n}.

(ii) Write indexed NP relations as REL = {(𝐢, 𝐱, 𝐰)}. For any relation REL, let ℒ(REL) = {(𝐢, 𝐱) |
     ∃𝐰 : (𝐢, 𝐱, 𝐰) ∈ REL} denote the language corresponding to REL.

(iii) Write ℛ_∂ for elements of a ring ℛ of bit-length less than or equal to some bound ∂ > 0.

(iv) Write 𝓜_{n×m}(ℛ) for a matrix ring over ℛ of dimension n×m.

(v) Write M @_{i,j} for the jth element of the ith row of a matrix M.

(vi) We distinguish operating symbols for logical objects from mathematical operations by using =̲,
     <̲, etc. rather than =, <, etc. for operations in FOL.

(vii) Write [·] for an oracle to a string or polynomial within the brackets.

(viii) Write π_ν for the projection taking a vector of length μ ≥ ν to its νth element. Thus
     π_ν(v_1, …, v_μ) = v_ν.

(ix) Given some boolean assertion Φ (i.e. a mathematical claim that is either true or false), define
     δ(Φ) the indicator of Φ such that δ(Φ) = 0 when Φ is true, and δ(Φ) = 1 when Φ is false.

(x) We may write function application as f(x) or as f x; meaning will always be clear.

▶ Definition 2.

1. Given a string s = (s_1, s_2, …, s_μ), define

                         b2int(s) = ∑_{1≤ν≤μ} s_ν · 2^{ν−1}.

   In this paper, either s will be a string of binary digits (so b2int(s) is an integer) or a string of variable symbols (so b2int(s) is a multivariate polynomial).

2. Given i ∈ ℕ, write ∅_b(i) for the binary decomposition of i.

▶ Lemma 3. For x ∈ ℕ, ∅_b(x) is the unique string of binary digits such that b2int(∅_b(x)) = x.


Multilinear Polynomials

▶ Definition 4. A multilinear polynomial over a ring ℛ is a multivariate polynomial

                 f(𝐗) = ∑_{i=1}^{<∞} a_i ∏_{j=1}^{μ} X_j^{e_{ij}}

in finitely many variables 𝐗 = (X_1, …, X_μ) with coefficients a_i ∈ ℛ, such that no variable occurs
in any homogeneous component with multiplicity larger than one; that is, 0 ≤ e_{ij} ≤ 1 for all i
and for all j ∈ [μ]. Write ℛ^{!!}[𝐗] for the set of multilinear polynomials in 𝐗 with coefficients
in ℛ.

▶ Definition 5. Given a function f : {0, 1}^μ → ℛ and a list of μ variables 𝐗, define f̃ ∈
  ℛ^{!!}[𝐗], the multilinear extension (MLE) of f, by

 f̃(X_1, …, X_μ) = ∑_{y∈{0,1}^μ} f(y) · eq(y, 𝐗),

 where  eq(y, 𝐗) = ∏_{i=1}^{μ} (y_i X_i + (1−y_i)(1−X_i)).

This is the unique multilinear polynomial in ℛ^{!!}[𝐗] which agrees with f on the μ-hypercube, by
which we mean that f(y) = f̃(y) for every y ∈ {0, 1}^μ [28].

▶ Definition 6. Given 𝐯 = (𝐯_0, …, 𝐯_{2^μ−1}) ∈ ℛ^{2^μ}, let f_𝐯 : {0, 1}^μ → ℛ take x to f_𝐯(x) =
  𝐯_{b2int(x)}, where we identify x-the-binary-string with the b2int(x)-th entry of 𝐯. E.g. f_𝐯(101)
  = 𝐯_5. Define the multilinear extension of 𝐯, f̃_𝐯, to be the multilinear extension of f_𝐯.


SNARKs and Algebraic Indexed Relations

A SNARK is a complete succinct non-interactive argument of knowledge satisfying knowledge soundness
(up to some error ε), allowing a prover to convince a verifier of knowledge of a witness satisfying
an instance of some relation REL = REL_gp, parameterised by global parameters gp.

We now explain these terms in more detail. We will obtain a SNARK by composing a transformation from
FOL to algebraic indexed relations (Definition 9) with Zinc-PIOP [18], and then applying the
transform of [6, 8] on Zinc-PIOP with the PCS Zip [18, Section 5]. We define PIOPs, via interactive
proofs, as follows:

▶ Definition 7 ([18, Definition 3.2]). An Interactive Proof (IP) for a relation REL_gp with global
  parameters gp is a triple of algorithms (Ind, P, V), where for all (𝐢, 𝐱, 𝐰) ∈ REL_gp, Ind is a
  deterministic algorithm taking (gp, 𝐢) as input and outputting verifier and prover parameters (vp,
  pp) ← Ind(gp, 𝐢). The pair (P, V) = (P(pp, 𝐱, 𝐰), V(vp, 𝐱)) is a pair of interactive algorithms
  with interaction denoted ⟨P, V⟩. An IP may satisfy

1. Completeness with completeness error ε_comp: for all (𝐢, 𝐱, 𝐰) ∈ REL_gp,

   Pr[⟨P(pp, 𝐱, 𝐰), V(vp, 𝐱)⟩ = 1 | (vp, pp) ← Ind(gp, 𝐢)]
       ≥ 1 − ε_comp(gp, 𝐢, 𝐱)

2. Soundness with error ε_s: for any unbounded adversarial prover P* and any (𝐢, 𝐱),

   Pr[⟨P*(pp, 𝐢, 𝐱), V(vp, 𝐱)⟩ = 1 ∧ (𝐢, 𝐱) ∉ ℒ(REL_gp)
      | (vp, pp) ← Ind(gp, 𝐢)]
       ≤ ε_s(gp, 𝐢, 𝐱)

3. Knowledge soundness with error ε_ks: there exists a probabilistic extractor Ext such that, given
   oracle access to any unbounded adversarial prover P* and any (𝐢, 𝐱),

   Pr[⟨P*(pp, 𝐢, 𝐱), V(vp, 𝐱)⟩ = 1 ∧ (𝐢, 𝐱, 𝐰) ∉ REL_gp
      | (vp, pp) ← Ind(gp, 𝐢), 𝐰 ← Ext_{P*}(gp, 𝐢, 𝐱)]
       ≤ ε_ks(gp, 𝐢, 𝐱, ε_{P*})

   where

   ε_{P*} = ε_{P*}(gp, 𝐢, 𝐱) = Pr[⟨P*(gp, 𝐢, 𝐱), V(vp, 𝐱)⟩ = 1].

This allows us to introduce (polynomial) interactive oracle proofs:

▶ Definition 8 ([18, Definitions 3.3, 3.4]). An interactive oracle proof (IOP) is an interactive
  proof for an indexed relation REL_gp = (𝐢, 𝐱, 𝐰) in which 𝐢 and 𝐱 may contain oracles to strings
  of elements from a ring ℛ.

A polynomial interactive oracle proof (PIOP) over a ring ℛ is an IOP such that all oracles contain
polynomials with coefficients in ℛ of prescribed number of variables μ and degrees. These
polynomials can be queried at any point of ℛ^μ.

Zinc-PIOP is defined for algebraic indexed relations, which as we will see comprise relations on
multilinear polynomials over ℚ, where coefficients are restricted to have bounded bit-length ∂ =
poly(λ) in the security parameter λ. Here the bit-length of a rational number is computed by writing
the rational number as a fraction in lowest terms, then computing the base-2 representations of the
numerator and denominator (padding the smaller of the two so that they are of equal bit-size), and
concatenating. This representation gives a bit-length of at most 2(log |a| + log b) + 3, where an
extra bit has been added to account for sign. Zinc’s relations are defined on the rationals but
honest provers are expected to use integer inputs.

We next formally define the relations used by Zinc; for the rest of this section, we fix an integral
domain ℛ ⊂ ℚ and a tuple of global parameters gp = (k, m, n, μ, ∂) of integers defining the
magnitudes and dimensions of the objects in Definition 9:

▶ Definition 9. Let 𝒬 be a set of multivariate polynomials with coefficients in a ring ℛ and let 𝐗 =
  (X_1, …, X_μ) denote μ variables. An algebraic indexed relation (AIR) [18, Definition 4.1] is a
  set REL_{gp,ℛ,𝒬} of triples (𝐢, 𝐱, 𝐰) such that:

1. The index 𝐢 is an n-tuple of oracles [g_1], …, [g_n] to multilinear polynomials with ∂-bounded
   coefficients, g_1, …, g_n ∈ ℛ_∂^{!!}[𝐗] for bit-length ∂ > 0.

2. The witness 𝐰 is a k-tuple of multilinear polynomials with ∂-bounded coefficients, f_1, …, f_k ∈
   ℛ_∂^{!!}[𝐗] for bit-length ∂ > 0.

3. The instance 𝐱 = ([f_1], …, [f_k], 𝐲) where 𝐲 ∈ ℛ_∂^m for some m ≥ 0 and the [f_i] are oracles to
   the elements in 𝐰.

4. 𝒬 is a set of multivariate polynomials with coefficients in ℛ in (n + k) · 2^μ + m variables,
   each of which vanishes (i.e. is equal to zero) when evaluated on the values

               ((g_1(𝐱), …, g_n(𝐱), f_1(𝐱), …, f_k(𝐱))_{𝐱∈{0,1}^μ}, 𝐲)

Summing this up in symbols, REL_{gp,ℛ,𝒬} has the following form:

REL_{gp,ℛ,𝒬} = {
  (𝐢, 𝐱, 𝐰) |
    gp = (k, m, n, μ, ∂),
    𝐢 = ([g_1], …, [g_n]),
    𝐱 = ([f_1], …, [f_k], 𝐲) for some 𝐲 ∈ ℛ_∂^m,
    𝐰 = (f_1, …, f_k) ∈ (ℛ_∂^{!!}[𝐗])^k,
    (g_1, …, g_n) ∈ (ℛ_∂^{!!}[𝐗])^n,
    Q((g_1(𝐱), …, g_n(𝐱), f_1(𝐱), …, f_k(𝐱))_{𝐱∈{0,1}^μ}, 𝐲) = 0
      for all Q ∈ 𝒬
}.                                                               (1)

▶ Remark 10. We can express CCS (an expressive constraint system) via Definition 9 [18, Section
  4.4]. We can also express range check/lookup relations [27], detailed in Appendix A.

Call an index-instance-witness triple for an AIR REL well-formed when it is of the form specified in
Definition 9. In particular, we assume throughout that malicious provers and adversaries use
well-formed instances of AIRs, and we assume that ℛ = ℤ. We thus remove the subscripted ring in our
relation definitions and write REL_{gp,𝒬} for AIRs.

We refer the reader to [18, Definition 3.5] for the definition of a PCS. A multilinear PCS is
succinct if it outputs commitments which are sublinear in 2^μ.


First-order logic

We set up the syntax and denotation of a simple first-order logic:

▶ Notation 11. Here and for the rest of the paper we fix the following syntactic data:

1. A set MVS of matrix variable symbols C ∈ MVS with fixed arities ar(C) ≥ 1.

2. A set BVar of quad-indexed variable symbols B_{i,ν}^{j,x} ∈ BVar, where i, j, x, ν ∈ ℕ.

3. A single index variable symbol X.

These variable symbols are all just formal symbols. We assume they are all distinct.

The arity ar(C) of a matrix variable symbol C is simply an associated positive integer. A sound and
complete polynomial semantics for first-order logic (FOL) from [15] used univariate polynomials and
their properties to soundly and completely capture the logical content of FOL predicates. [fn 7] We
now construct a simplified yet expressive FOL syntax (Figure 1) and a version of the semantics in
[15] (Figure 3) which are tailored to our needs in this paper.

[fn 7] A cryptographically oriented exposition is given in [14].


Term     t ::= q | t +̲ t | t ∗̲ t | len(C) | reify(ϕ) | X | C_i(X) | C_i C_j(X)
Pred  ϕ, ψ ::= t =̲ t | ϕ ∧̲ ϕ | ϕ ∨̲ ϕ
RCheck   R ::= ∅ | R, t <̲ C_i | R, C_i <̲ t
EP       P ::= q | P +̲ P | P ∗̲ P | len(C) | X | C_i(X) | C_i C_j(X)
                   (i, j ∈ [ar(C)], q ∈ ℤ)

Figure 1. Terms, predicates, range checks, and enriched polynomials (Definition 12(1))


Terms

  ⟨q⟩ = q  (q ∈ ℤ)         ⟨t +̲ t′⟩ = ⟨t⟩ + ⟨t′⟩         ⟨C_i(X)⟩ = C_i(X)
  ⟨X⟩ = X                   ⟨t ∗̲ t′⟩ = ⟨t⟩ ∗ ⟨t′⟩         ⟨C_i C_j(X)⟩ = C_i C_j(X)
  ⟨len(C)⟩ = len(C)         ⟨reify(ϕ)⟩ = ⟨ϕ⟩

Predicates

  ⟨t =̲ t′⟩ = (⟨t⟩ − ⟨t′⟩)^2
  ⟨ϕ ∧̲ ϕ′⟩ = ⟨ϕ⟩ + ⟨ϕ′⟩
  ⟨ϕ ∨̲ ϕ′⟩ = ⟨ϕ⟩ ∗ ⟨ϕ′⟩

Figure 2. From Term and Pred to enriched polynomials EP (Definition 12(3))


▶ Definition 12.

1. Define syntaxes of terms, predicates, and enriched polynomials as per the BNF grammar in Figure
   1.

2. Write ⊤ as sugar for (0 =̲ 0), and ⊥ for (0 =̲ 1).

3. Define a mapping ⟨·⟩ taking terms and predicates to enriched polynomials as in Figure 2.

▶ Remark 13 (Some comments on Definition 12). Pred is a simple predicate language of conjunctions
  and disjunctions over equalities. True is expressed as 0 =̲ 0 and false as 0 =̲ 1. A
  quantification over the index variable symbol X is implicit in the syntax, as will become explicit
  later in Definition 20(3&4) and Lemma 21.

Pred only has one index variable symbol X, and one polynomial function symbol C. In general one
might want more, but even in its current form Pred is actually very expressive and not a toy: in
particular, it can express the full list of examples from [15].

Enriched polynomials are a subsyntax of terms; we will exploit this fact below.

▶ Lemma 14. If t ∈ Term and ϕ ∈ Pred then ⟨t⟩ and ⟨ϕ⟩ are enriched polynomials.

Proof. By a routine induction (from Figure 2). ◀

▶ Remark 15. Why are ⟨·⟩ and enriched polynomials interesting?

1. We can map t ∈ Term and ϕ ∈ Pred (Figure 1) to enriched polynomials as per Lemma 14.

2. We can map enriched polynomials to actual multivariate polynomials, as per Figure 4.

Items 1 and 2 show that enriched polynomials are therefore a bridge between logic and multivariate
polynomials. After establishing this bridge,

3. We can evaluate the variables in the resulting polynomials generated by mkQ_ℱ^x using β_ℱ
   (Definition 25), such that (by Theorem 27) the composition β_ℱ ◦ mkQ_ℱ^x ◦ ⟨·⟩ coincides (by
   Theorem 19) with the sound and complete integer semantics for FOL ⟨·⟩_ς^x from Figure 3.

4. We can use the above machinery to generate polynomial relations compatible with Zinc.


Integer Semantics for FOL

In this section we define ⟨·⟩_ς^x (see Figure 3), describing a sound and complete integer semantics
for FOL.

▶ Definition 16 (FOL semantics). 1. We define an interpretation to be a map

                 ς : MVS → 𝓜_{ar(C)×ℓ_ς(C)}(ℕ),      C ↦ ς(C)

⟨q⟩_ς^x = q
⟨X⟩_ς^x = x
⟨len(C)⟩_ς^x = len(ς(C))

⟨t +̲ t′⟩_ς^x = ⟨t⟩_ς^x + ⟨t′⟩_ς^x
⟨t ∗̲ t′⟩_ς^x = ⟨t⟩_ς^x ∗ ⟨t′⟩_ς^x
⟨reify(ϕ)⟩_ς^x = ⟨ϕ⟩_ς^x

⟨C_i(X)⟩_ς^x = ς(C)@_{i,x}
⟨C_i C_j(X)⟩_ς^x = ς(C)@_{i,ς(C)@_{j,x}}

⟨t =̲ t′⟩_ς^x = (⟨t⟩_ς^x − ⟨t′⟩_ς^x)²
⟨ϕ ∧̲ ϕ′⟩_ς^x = ⟨ϕ⟩_ς^x + ⟨ϕ′⟩_ς^x
⟨ϕ ∨̲ ϕ′⟩_ς^x = ⟨ϕ⟩_ς^x ∗ ⟨ϕ′⟩_ς^x

⟨∅⟩_ς = 0
⟨R, C_i <̲ t⟩_ς = ⟨R⟩_ς + δ(∀x∈[len(ς(C))]. ⟨t⟩_ς^x > ς(C)@_{i,x})
⟨R, t <̲ C_i⟩_ς = ⟨R⟩_ς + δ(∀x∈[len(ς(C))]. ⟨t⟩_ς^x < ς(C)@_{i,x})

Above: δ is the indicator function from Notation 1(ix), and @_{i,x} is from Notation 1(v).

Figure 3. Integer semantics for FOL terms, predicates, and range checks (Definition 16)

where ℓ_ς(C) ∈ ℕ_{≥1} depends on ς. [fn 8]

2. Suppose t ∈ Term and ϕ ∈ Pred and R ∈ RCheck and x ∈ [ℓ_ς(C)] and ς is an
   interpretation. Define a semantics ⟨t⟩_ς^x ∈ ℤ, ⟨ϕ⟩_ς^x, ⟨R⟩_ς ∈ ℕ as per Figure 3.

Definition 16 might seem odd: FOL already has a well-known Boolean truth-valued semantics,
so: a) why give it an integer semantics, and b) what does this integer semantics even mean?
In reply: we give FOL an integer semantics because it will help us arithmetise FOL in
Section 3. As to what the semantics means, we can sum this up using two slogans:

1. Slogan 1. Zero = true; non-zero = false. We treat ℕ as a domain of truth-values in which
   zero is the single designated ‘true’ truth-value, and non-zero values are ‘false’.

2. Slogan 2. Equality = square of difference; conjunction = sum; disjunction = product.
   This just reads off the relevant clauses in Figure 3.

These slogans are mathematically justified by Lemma 17 and Theorem 19.

▶ Lemma 17 (Non-negativity). Suppose ϕ ∈ Pred and ς is an interpretation. Then
⟨ϕ⟩_ς^x ≥ 0.

Proof. We consider ⟨ϕ⟩_ς^x in Figure 3: ⟨t =̲ t′⟩_ς^x is a square and squares are
non-negative (even if ⟨t⟩_ς^x or ⟨t′⟩_ς^x are negative); ⟨ϕ ∧̲ ϕ′⟩_ς^x is a sum and sums
of non-negatives are non-negative; ⟨ϕ ∨̲ ϕ′⟩_ς^x is a product and products of
non-negatives are non-negative. ◀

▶ Definition 18 (Validity). Suppose ϕ ∈ Pred and R ∈ RCheck and ς is an interpretation
on C and x ∈ [len(ς(C))]. Then write x ⊨_ς ϕ when ⟨ϕ⟩_ς^x = 0, and write ⊨_ς R
when ⟨R⟩_ς = 0.

▶ Theorem 19 (Soundness and completeness). Suppose ϕ, ϕ′ ∈ Pred, and t, t′ ∈ Term, and
R ∈ RCheck. Suppose ς is an interpretation, and write ℓ = len(ς(C)). Suppose x ∈ [ℓ]. Then:

1. x ⊨_ς t =̲ t′ if and only if ⟨t⟩_ς^x = ⟨t′⟩_ς^x.
2. x ⊨_ς ⊤ and x ⊭_ς ⊥ (by Definition 12(2) ⊤ is sugar for 0 =̲ 0 and ⊥ is sugar for 0 =̲ 1).
3. x ⊨_ς ϕ ∧̲ ϕ′ if and only if x ⊨_ς ϕ ∧ x ⊨_ς ϕ′.
4. x ⊨_ς ϕ ∨̲ ϕ′ if and only if x ⊨_ς ϕ ∨ x ⊨_ς ϕ′.
5. ⊨_ς ∅.
6. ⊨_ς R, t <̲ C_i if and only if ⊨_ς R ∧ ∀x∈[ℓ]. ⟨t⟩_ς^x < ς(C)@_{i,x}.
7. ⊨_ς R, C_i <̲ t if and only if ⊨_ς R ∧ ∀x∈[ℓ]. ς(C)@_{i,x} < ⟨t⟩_ς^x.

Proof. See Appendix B. ◀

[fn 8] Letting ς(C) be a matrix of non-negative numbers is convenient because it simplifies b2int
and ∅_b in Definition 2 (there is no need to worry about binary representations of negative
numbers). We can still get negative numbers in terms t using addition and multiplication by
q ∈ ℤ.


mkQ_ℱ^x(q) = q
mkQ_ℱ^x(len(C)) = ℓ
mkQ_ℱ^x(X) = x

mkQ_ℱ^x(P +̲ P′) = mkQ_ℱ^x(P) + mkQ_ℱ^x(P′)
mkQ_ℱ^x(P ∗̲ P′) = mkQ_ℱ^x(P) ∗ mkQ_ℱ^x(P′)
mkQ_ℱ^x(C_i(X)) = b2int(B_{i,1}^{0,x}, …, B_{i,maxbl}^{0,x})
mkQ_ℱ^x(C_i C_j(X)) = b2int(B_{i,1}^{j,x}, …, B_{i,maxbl}^{j,x})

Here i ∈ [ar(C)], j ∈ {0} ∪ [ar(C)], maxbl, ℓ ∈ ℕ_{≥1}, x ∈ [ℓ], and
ℱ = (f_i : [ℓ] → ℕ | i ∈ [ar(C)]).

Note that j ∈ {0} ∪ [ar(C)] yet C_0(X) is not defined - this will not trouble us because a
FOL validity predicate will never transform to an enriched polynomial supported on C_0(X).

Figure 4. From enriched polynomials EP to multivariate polynomials MVP (Definition 24)


3  Arithmetising FOL

We now show how to arithmetise the FOL syntax from Figure 1, i.e. to map FOL to polynomials
that match up, in a sense made formal by Theorem 27, with the integer semantics of
Theorem 19.

▶ Definition 20.

1. Say ϕ ∈ Pred uses C_j as a pointer when ϕ contains a subterm of the form C_i C_j(X).

2. Say (ϕ, R) ∈ Pred × RCheck is range-checked when for every j such that ϕ uses C_j as a
   pointer, R contains conditions of the form 0 <̲ C_j and C_j <̲ len(C) +̲ 1.

3. A judgement is a 3-tuple, written C ⊨_ς ϕ; R, of: an interpretation ς; a predicate
   ϕ ∈ Pred; and a range check R ∈ RCheck; such that (ϕ, R) is range-checked.

4. Call a judgement C ⊨_ς ϕ; R valid when: ⟨ϕ⟩_ς^x = 0 for every x ∈ [len(ς(C))], and
   ⟨R⟩_ς = 0.

5. We may write C ⊨_ς ϕ; ∅ just as C ⊨_ς ϕ, and we may write C ⊨_ς ⊤; R just as C ⊨_ς R.

▶ Lemma 21. Let ϕ ∈ Pred, R ∈ RCheck, ς be an interpretation, and ℓ = len(ς(C)). Then:

1. C ⊨_ς ϕ when ⟨ϕ⟩_ς^x = 0 (equivalently using Definition 18: x ⊨_ς ϕ) for every
   x ∈ [ℓ]. Note C ⊨_ς ϕ has the flavour of a universal quantification of ϕ for X ranging
   over x ∈ [ℓ].

2. C ⊨_ς R when ⟨R⟩_ς = 0 (equivalently: ⊨_ς R).

   We unpack what this means using Theorem 19(6&7): for every x ∈ [ℓ] we have
   ⟨t⟩_ς^x < ς(C)@_{i,x} for every t <̲ C_i in R, and ⟨t⟩_ς^x > ς(C)@_{i,x} for every
   C_i <̲ t appearing in R.

Proof. Direct from Definition 20. ◀

▶ Remark 22. As per Lemma 21, C ⊨_ς ϕ; R being valid has the flavour of a universal
quantification that ϕ and R are valid for every x ∈ [ℓ]. This gives our syntax from Figure 1
some extra expressivity, in that the index variable X is universally quantified over [ℓ].

▶ Remark 23. We continue Remark 15: predicates ϕ ∈ Pred (Figure 1) can express equality,
conjunction, and disjunction on terms that include C_i(X) and C_i C_j(X). Range checks
R ∈ RCheck can express range checks on the C_i.

The integer semantics from Figure 3 maps this syntax to integers, and Theorem 19 shows that
this fits together in the sense that with these definitions, validity of predicates and range
checks behaves in the way that the symbols would lead us to expect. For example:
x ⊨_ς ϕ ∧̲ ϕ′ is indeed valid if and only if x ⊨_ς ϕ is valid and x ⊨_ς ϕ′ is valid; and
t <̲ C_i is indeed valid when ⟨t⟩_ς^x is a lower bound for the entries of the ith row of ς(C).

As per Remark 15, we will now connect our integer semantics to a multivariate polynomial
semantics which we build using the enriched polynomials from Figure 2.

We now define mkQ (read ‘make Q’) taking enriched polynomials to multivariate polynomials.
Intuitively, mkQ_ℱ^x is what computes the polynomials Q ∈ 𝒬 used in equation (1).

We pad binary expansions of the elements of the images of the f_i ∈ ℱ so that all binary
expansions have the same length, equal to the largest bit-length obtaining over all the ranges
of the f_i. Write maxbl for the maximum bit-length of the elements in the images of the f_i.

▶ Definition 24. Suppose maxbl, ℓ > 0, x ∈ [ℓ], and ℱ = (f_i : [ℓ] → ℕ | i ∈ [ar(C)]). Define
mkQ_ℱ^x mapping enriched polynomials (Definition 12(1)) to multivariate polynomials

  mkQ_ℱ^x : EP → ℤ[B_{1,1}^{0,1}, …, B_{1,maxbl}^{0,1}, …,
                    B_{ar(C),1}^{ar(C),ℓ}, …, B_{ar(C),maxbl}^{ar(C),ℓ}]

as per Figure 4.

Next we define an evaluation map β_ℱ as a composition of the π_ν, ∅_b, and the f_i:

▶ Definition 25. Suppose maxbl, ℓ > 0 and ℱ = (f_i : [ℓ] → ℕ | i ∈ [ar(C)]). [fn 9] Then:

1. For each i ∈ [ar(C)] and j ∈ [ar(C)] and x ∈ [ℓ] and ν ∈ [maxbl], define β_ℱ by

   β_ℱ(B_{i,ν}^{0,x}) = π_ν ∅_b f_i(x)

   and

                           ⎧ π_ν ∅_b f_i(f_j(x))   if f_j(x) ∈ [ℓ]
   β_ℱ(B_{i,ν}^{j,x}) = ⎨
                           ⎩ 0                     if f_j(x) ∉ [ℓ].

   Thus in words: β_ℱ maps B_{i,ν}^{0,x} to the νth bit of the binary expansion of f_i(x);
   and β_ℱ maps B_{i,ν}^{j,x} to the νth bit of the binary expansion of f_i(f_j(x)) (if this
   is in-range, Definition 26).

2. We extend β_ℱ to an evaluation map on multivariate polynomials in the natural way by
   instantiating variable symbols. E.g. β_ℱ(0 + B_{1,3}^{0,2} ∗ B_{4,6}^{0,5}) =
   0 + (π_3 ∅_b f_1(2)) ∗ (π_6 ∅_b f_4(5)).

▶ Definition 26. Suppose ℱ = (f_i : [ℓ] → ℕ | i ∈ [ar(C)]) and t ∈ Term and ϕ ∈ Pred.
Call ℱ in-range for t / for ϕ when for every j that t / ϕ uses as a pointer, we have
∀x ∈ [ℓ]. 1 ≤ f_j(x) ≤ ℓ.

A central technical result is that β_ℱ ∘ mkQ_ℱ^x ∘ ⟨·⟩ equals ⟨·⟩_ς^x:

▶ Theorem 27. Suppose t ∈ Term and ϕ ∈ Pred and ς is an interpretation. Write
ℓ = len(ς(C)) and suppose x ∈ [ℓ]. Define

  ℱ = (f_i = (x∈[ℓ] ↦ ς(C)@_{i,x}) | i ∈ [ar(C)]).

If ℱ is in-range for t and ϕ (Definition 26), then:

  β_ℱ(mkQ_ℱ^x⟨t⟩) = ⟨t⟩_ς^x    and    β_ℱ(mkQ_ℱ^x⟨ϕ⟩) = ⟨ϕ⟩_ς^x.

Proof. Routine induction on syntax. The interesting cases are for X, C_i(X), and C_i C_j(X):

  β_ℱ(mkQ_ℱ^x⟨X⟩) = β_ℱ(mkQ_ℱ^x X)                                      Figure 2
                     = β_ℱ(x)                                           Figure 4
                     = x                                                Def. 25(2)
                     = ⟨X⟩_ς^x                                           Figure 3

  β_ℱ(mkQ_ℱ^x⟨C_i(X)⟩) = β_ℱ(b2int(B_{i,1}^{0,x}, …, B_{i,maxbl}^{0,x}))      Figures 2 & 4
                          = b2int(∅_b f_i(x))                              Def. 25
                          = f_i(x)                                        Lemma 3
                          = ς(C)@_{i,x}                                   Def. of ℱ, x ∈ [ℓ]
                          = ⟨C_i(X)⟩_ς^x                                  Figure 3

  β_ℱ(mkQ_ℱ^x⟨C_i C_j(X)⟩) = β_ℱ(b2int(B_{i,1}^{j,x}, …, B_{i,maxbl}^{j,x}))   Figures 2 & 4
                              = f_i(f_j(x))                             Def. 25 & Lemma 3
                              = ς(C)@_{i,ς(C)@_{j,x}}                   Def. of ℱ, f_j(x) ∈ [ℓ]
                              = ⟨C_i C_j(X)⟩_ς^x                          Figure 3

◀

[fn 9] In the case of a cryptographic application to arithmetise FOL relations to AIRs, a verifier V
will not have direct access to the f_i, instead having oracle access to them via a polynomial
commitment scheme.

▶ Corollary 28. Suppose ς is an interpretation such that ς(C) ∈ 𝓜_{ar(C)×ℓ}(ℕ). Suppose
C ⊨ ϕ; R is a judgement (so that ϕ ∈ Pred and R ∈ RCheck and (ϕ, R) is properly
range-checked). Define ℱ = (f_i = (x∈[ℓ] ↦ ς(C)@_{i,x}) | i ∈ [ar(C)]). Then:

  C ⊨_ς ϕ; R    if and only if    ∀x ∈ [ℓ]. β_ℱ(mkQ_ℱ^x⟨ϕ⟩) = 0  ∧
                                 ∀x ∈ [ℓ]. β_ℱ(mkQ_ℱ^x⟨t⟩) < ς(C)@_{i,x}
                                   for every t <̲ C_i in R  ∧
                                 ∀x ∈ [ℓ]. β_ℱ(mkQ_ℱ^x⟨t⟩) > ς(C)@_{i,x}
                                   for every C_i <̲ t in R.

Proof. Routine from Theorem 27 and Lemma 21. Theorem 27 requires ℱ be in-range
(Definition 26); this follows from our assumption that (ϕ, R) is range-checked
(Definition 20(2)). ◀


4  An integer SNARK for Relations in First-Order Logic

Below, we describe in Lemma 30 how to transform instances of relations defined in
first-order logic to instances of relations defined using multivariate polynomials, using
Corollary 28. These latter relations are suitable inputs to Zinc-PIOP. We do not require
auxiliary data in the index 𝐢, so we only consider instance-witness pairs (𝐱, 𝐰) below. We
first define relations for predicates in Pred and range checks in RCheck:

▶ Definition 29. Suppose ϕ ∈ Pred (the predicate language from Figure 1), and R ∈ RCheck,
and ς is an interpretation. Let ℓ = len(ς(C)). Define two relations:

  REL_gp^FOL = { ((ϕ, R), ς) | ς(C) ∈ 𝓜_{ar(C)×ℓ}(ℕ),  C ⊨_ς ϕ; R }    and

  REL_gp^EP  = { ((⟨ϕ⟩, R), ς(C)) | ς(C) ∈ 𝓜_{ar(C)×ℓ}(ℕ),  C ⊨_ς ϕ; R }.

The relation REL_gp^EP is an intermediate relation obtained by turning instances of
REL_gp^FOL into enriched polynomials, via Figure 2. By converting ϕ to ⟨ϕ⟩, we obtain an
enriched polynomial instance preserving the logical content of ϕ, with a witness 𝐰 = ς being
knowledge of ς(C) ∈ 𝓜_{ar(C)×ℓ}(ℕ) satisfying ϕ.

We now use mkQ_ℱ^x (Figure 4) to map enriched polynomials to multivariate polynomials,
setting ℱ = (f̃^i_{ς(C)} | i ∈ [ar(C)]), i.e. ℱ comprises the multilinear extensions of the
rows of ς(C). Note that, before padding, the f̃^i_{ς(C)} are multilinear polynomials in
μ = ⌈log₂ ℓ⌉ variables. However, for pointer correctness, we pad so that
μ = max(⌈log₂ ℓ⌉, maxbl). [fn 10]

By Corollary 28, with ℱ = (f̃^i_{ς(C)} | i ∈ [ar(C)]) and

  f̃^i_{ς(C)}(f̃^j_{ς(C)}(x)) := f̃^i_{ς(C)}(∅_b f̃^j_{ς(C)}(x)),

we have that REL_gp^EP of Definition 29 is equivalent to

  REL_{gp,ℱ}^MV =
    { (((mkQ_ℱ^x⟨ϕ⟩)_{x∈[ℓ]}, R), (f̃^i_{ς(C)})_{i∈[ar(C)]}) |
        ς(C) ∈ 𝓜_{ar(C)×ℓ}(ℕ),  C ⊨_ς R,
        ∀x∈[ℓ](β_ℱ(mkQ_ℱ^x⟨ϕ⟩) = 0) }.

By choosing ℱ = {f̃^i_{ς(C)} | i ∈ [ar(C)]}, we find that the condition that the image of
β_ℱ on the multivariate polynomial mkQ_ℱ^x⟨ϕ⟩ satisfies β_ℱ(mkQ_ℱ^x⟨ϕ⟩) = 0 is equivalent
to mkQ_ℱ^x⟨ϕ⟩ evaluating to zero at some subset of

  (∅_b(ς(C)@_{1,1}), …, ∅_b(ς(C)@_{ar(C),ℓ}))
    = (∅_b f̃^1_{ς(C)}(∅_b 1), …, ∅_b f̃^{ar(C)}_{ς(C)}(∅_b ℓ))

(recall from Notation 1(v) that ς(C)@_{i,j} is the i, jth entry of ς(C)) as long as the
range checks in R guarantee that any pointer C_i(X) in ϕ corresponds to a row ς(C)_i with
entries bounded by len(ς(C)). We now prove that REL_{gp,ℱ}^MV provides algebraic indexed
relations:

[fn 10] More explicitly, the f̃^i_{ς(C)} have domain [len(ς(C))], so inputs are of bit length at
        most
⌈log₂(len(ς(C)))⌉ = μ, and have range comprising elements of bit length at most maxbl. To
form the composition f̃^i_{ς(C)}(∅_b f̃^j_{ς(C)}), we require that the length of ∅_b f̃^j_{ς(C)}
is identical to the bit length of inputs to f̃^i_{ς(C)}.

▶ Lemma 30. Let gp_0, gp_1 denote global parameters, and fix ∂, μ > 0. Let ϕ be a predicate
defined over ℤ in a matrix variable symbol C. Let ς(C) ∈ 𝓜_{ar(C)×ℓ}(ℕ) be an interpretation,
and R be a set of range check conditions on ς(C). Set

  ℱ = {f̃^i_{ς(C)} ∈ ℤ_∂^{!!}[𝐗] | i ∈ [ar(C)]}.

Then the data of an instance of REL_{gp_0}^EP can be expressed as a pair (𝐱, 𝐰) of
REL_{gp_1,𝒬} for some gp_1 and some 𝒬, such that (𝐱, 𝐰) is well-formed if and only if
C ⊨_ς ϕ; R is valid.

Proof. Let

  (((mkQ_ℱ^x⟨ϕ⟩)_{x∈[len(ς(C))]}, R), (f̃^i_{ς(C)})_{i∈[ar(C)]}) ∈ REL_{gp,ℱ}^MV

be obtained from the instance ((ϕ, R), ς) ∈ REL_{gp_0}^EP. We first define an AIR,
REL_{gp′,𝒬′}, corresponding to (mkQ_ℱ^x⟨ϕ⟩)_{x∈[len(ς(C))]}. Set the instance-witness pair
in REL_{gp′,𝒬′} to be

  (𝐱, 𝐰) = (([f̃^1_{ς(C)}], …, [f̃^{ar(C)}_{ς(C)}]),
            (f̃^1_{ς(C)}, …, f̃^{ar(C)}_{ς(C)}))

where [·] denotes an oracle to the argument, [fn 11] and set

  𝒬′ = (mkQ_ℱ^x⟨ϕ⟩)_{x∈[len(ς(C))]}.

These data represent an AIR for some gp′: for each x ∈ [len(ς(C))], mkQ_ℱ^x⟨ϕ⟩ is a
multivariate polynomial determined by ϕ, evaluating to zero on a subset of the binary
decompositions

  (∅_b f̃^1_{ς(C)}(∅_b 1), …, ∅_b f̃^{ar(C)}_{ς(C)}(∅_b len(ς(C))))

We also append polynomials of the form

  B_{i,1}^{j,x}(B_{i,1}^{j,x} − 1), …, B_{i,μ}^{j,x}(B_{i,μ}^{j,x} − 1)

to 𝒬′; for each response from the oracle the verifier will check the vector has length μ and
use the B_{i,ν}^{j,x}(B_{i,ν}^{j,x} − 1) to ensure that the oracle has returned data of the
correct data type, namely bits.

Next, since a range check may be encoded as an AIR (equation (2)), for all range check
conditions in R we form a corresponding AIR with a set of defining polynomials 𝒬_R and
global parameters gp″. We then combine the two AIRs we have constructed, setting
𝒬 := 𝒬′ ∪ 𝒬_R, appending the instance-witness data of the range check relation to the former
relation REL_{gp′,𝒬′}, and denoting the updated global parameters by gp_1.

The claim that (𝐱, 𝐰) is well-formed if and only if C ⊨_ς ϕ; R is direct from Corollary 28:
well-formed (𝐱, 𝐰) have integer entries and satisfy the polynomial relations in 𝒬, whose
constraints guarantee that C ⊨_ς ϕ and C ⊨_ς R. The converse holds by construction. ◀

For instances ((ϕ, R), ς) to generate valid inputs to Zinc, they must also be well-formed:

▶ Definition 31. An instance ((ϕ, R), ς) ∈ REL_gp^FOL is well-formed if it transforms via the
transform described in Lemma 30 to an instance of REL_{gp,𝒬}, for some ℱ and 𝒬, which is
well-formed as an algebraic indexed relation.

Lemma 30 shows that we may efficiently compile well-formed instance-witness pairs defined
in the syntax of FOL (matrix variable symbols and enriched polynomials) into AIR
instance-witness pairs which are valid inputs to Zinc-PIOP. Once we have instance-witness
pairs of a form which may be provided as the input to a PIOP (such as Zinc-PIOP), we can
commit to the witness data using a PCS and compile the PIOP to obtain a SNARK.

[fn 11] Which oracle will later be instantiated with a PCS such as Zip [18, Section 5].

Observe from Figure 4 that mkQ_ℱ^x⟨ϕ⟩ may contain subterms corresponding to C_i C_j(X), whose
indices depend on evaluations f_j(x) = f̃^j_{ς(C)}(∅_b x). Recall further that such f̃^j_{ς(C)} are
‘pointers’ obtained by interpolating rows of ς(C). Since these values (equivalently, interpolating
polynomials) are not public, but rather are part of the witness inside a polynomial commitment, when
running a PIOP on the relations constructed in Lemma 30 we stipulate that a verifier who verifies
that β_ℱ(mkQ_ℱ^x⟨ϕ⟩) = 0 must first query the commitments [f̃^j_{ς(C)}(X₁, . . . , X_μ)] ∈ 𝐱 for ∅_b
f̃^j_{ς(C)}(∅_b x) for all j for which ς(C)_j acts as a pointer, which values then define mkQ_ℱ^x⟨ϕ⟩.
We assume the PCS returns the bits of the queried entry of the witness data. Aside from this
additional step, our SNARK uses a multilinear PCS to provide input relations for a PIOP which is run
in an otherwise standard manner.

▶ Corollary 32. Let λ denote a security parameter. Suppose ϕ ∈ Pred and R ∈ RCheck and ς is an
  interpretation satisfying ς(C) ∈ 𝓜_{ar(C)×len(ς(C))}(ℕ), with ar(C), len(ς(C)) ∈ ℤ_{≥1} satisfying
  ar(C) = poly(λ), len(ς(C)) = poly(λ). Set μ := maxbl. Set ℱ = {f̃^i_{ς(C)} ∈ ℤ_∂^{!!}[𝐗] | i ∈
  [ar(C)]} for some ∂ > 0. Then there exists a SNARK to convince a verifier that a well-formed
  instance ((ϕ, R), ς) ∈ REL_gp^FOL satisfies C ⊨_ς ϕ; R, with soundness error ε_sound equal to the
  soundness error of Zinc, instantiated with global parameters gp = (ar(C), 0, 1, (|R| + 2)μ, ∂).

Proof. See Appendix C. ◀

▶ Remark 33. The verifier complexity of our SNARK is inherited from the verifier complexity of the
  SNARK used under the hood of Zinc. The verifier sees a proof, which they verify. The prover
  complexity is more complicated. If the input instance is defined on the len(ς(C)) polynomials
  (mkQ_ℱ^x⟨ϕ⟩)_{x∈[len(ς(C))]}, then the prover complexity is also directly inherited from the
  prover complexity of Zinc’s SNARK.

However, if the input instance is defined from an arbitrary FOL predicate, then the prover must
perform the transformations of Figures 2 and 4 to obtain the mkQ_ℱ^x⟨ϕ⟩. For an arbitrary predicate
ϕ this may be computationally intensive. However, in practice provers do not generate arbitrary ϕ;
they generate ϕ with specific structure reflecting specific meaning. Thus there is a design space of
optimal syntactic forms for predicates, to optimise proving. This is a familiar pattern: design
spaces of optimal syntactic forms are known for other computational applications of logic (e.g. the
Horn clause theories of logic-programming). We leave as an open question the task of preprocessing
the input FOL relations into a logically equivalent form which arithmetises to an AIR of lowest
complexity.

▶ Remark 34. We note that the set 𝒬′ contains len(ς(C)) polynomials mkQ_ℱ^x⟨ϕ⟩. Moreover, the
  equivalence between the initial FOL instance and the instance we construct as an input to
  Zinc-PIOP holds only if β_ℱ(mkQ_ℱ^x⟨ϕ⟩) = 0 for all x ∈ [len(ς(C))]. To avoid checking that each
  and every mkQ_ℱ^x⟨ϕ⟩ evaluates to zero under β_ℱ, we can run a ‘random linear combinations’ step
  in which the verifier sends ℓ_ς(C) = len(ς(C)) uniformly random challenges c_i from a suitable
  challenge set and the prover proves that the random linear combination

    ℓ_ς(C)
       ∑     c_x · mkQ_ℱ^x⟨ϕ⟩
      x=1

satisfies

       ⎛ ℓ_ς(C)                   ⎞
    β_ℱ⎜    ∑     c_x · mkQ_ℱ^x⟨ϕ⟩⎟ = 0.
       ⎝   x=1                      ⎠

This comes at the cost of a small increase in the soundness error of the protocol, and the details
are beyond the scope of this paper.


References

1. Logan Allen, Brian Klatt, Philip Quirk, and Yaseen Shaikh. EDEN - a practical, SNARK-friendly
   combinator VM and ISA. Cryptology ePrint Archive, Paper 2023/1021, 2023. URL:
   https://eprint.iacr.org/2023/1021.

2. Sebastian Angel, Eleftherios Ioannidis, Elizabeth Margolin, Srinath Setty, and Jess Woods. Reef:
   Fast succinct Non-Interactive Zero-Knowledge regex proofs. In 33rd USENIX Security Symposium
   (USENIX Security 24), pages 3801–3818, Philadelphia, PA, August 2024. USENIX Association. URL:
   https://www.usenix.org/conference/usenixsecurity24/presentation/angel.

3. Lennart Augustsson. MicroHs: A small compiler for Haskell. In Proceedings of the 17th ACM SIGPLAN
   International Haskell Symposium, Haskell 2024, pages 120–124, New York, NY, USA, 2024.
   Association for Computing Machinery. doi:10.1145/3677999.3678280.

4. Jon Barwise. An introduction to first-order logic. In Jon Barwise, editor, Handbook of
   Mathematical Logic, volume 90 of Studies in Logic and the Foundations of Mathematics, pages 5–46.
   North-Holland, Amsterdam, 1977. doi:10.1016/S0049-237X(08)71097-8.

5. Eli Ben-Sasson, Alessandro Chiesa, Daniel Genkin, Eran Tromer, and Madars Virza. SNARKs for C:
   Verifying program executions succinctly and in zero knowledge. In Ran Canetti and Juan A. Garay,
   editors, Advances in Cryptology – CRYPTO 2013, volume 8043 of Lecture Notes in Computer Science,
   pages 90–108. Springer, Berlin, Heidelberg, 2013. doi:10.1007/978-3-642-40084-1_6.

6. Eli Ben-Sasson, Alessandro Chiesa, and Nicholas Spooner. Interactive oracle proofs. In Martin
   Hirt and Adam Smith, editors, Theory of Cryptography, volume 9986 of Lecture Notes in Computer
   Science, pages 31–60. Springer, Berlin, Heidelberg, 2016. doi:10.1007/978-3-662-53644-5_2.

7. Alexander R. Block, Zhiyong Fang, Jonathan Katz, Justin Thaler, Hendrik Waldner, and Yupeng
   Zhang. Field-agnostic SNARKs from expand-accumulate codes. In Leonid Reyzin and Douglas Stebila,
   editors, Advances in Cryptology – CRYPTO 2024, volume 14929 of Lecture Notes in Computer Science,
   pages 276–307, Cham, 2024. Springer Nature Switzerland. doi:10.1007/978-3-031-68403-6_9.

8. Benedikt Bünz, Ben Fisch, and Alan Szepieniec. Transparent SNARKs from DARK compilers. In Anne
   Canteaut and Yuval Ishai, editors, Advances in Cryptology – EUROCRYPT 2020, volume 12105 of
   Lecture Notes in Computer Science, pages 677–706. Springer, Cham, 2020.
   doi:10.1007/978-3-030-45721-1_24.

9. Matteo Campanelli and Mathias Hall-Andersen. Fully succinct arguments over the integers from
   first principles. Cryptology ePrint Archive, Paper 2024/1548, 2024. URL:
   https://eprint.iacr.org/2024/1548.

10. Matteo Campanelli and Mathias Hall-Andersen. General techniques for building SNARKs over the
    integers. In Shi Bai and Edoardo Persichetti, editors, Public-Key Cryptography – PKC 2026,
    volume 16553 of Lecture Notes in Computer Science, pages 197–230, Cham, 2026. Springer Nature
    Switzerland. doi:10.1007/978-3-032-26737-5_7.

11. T. J. W. Clarke, P. J. S. Gladstone, C. D. MacLean, and A. C. Norman. SKIM – the S, K, I
    reduction machine. In Proceedings of the 1980 ACM Conference on LISP and Functional Programming,
    LFP ’80, pages 128–135, New York, NY, USA, 1980. Association for Computing Machinery.
    doi:10.1145/800087.802798.

12. Benjamin E. Diamond and Jim Posen. Succinct arguments over towers of binary fields. In Serge
    Fehr and Pierre-Alain Fouque, editors, Advances in Cryptology – EUROCRYPT 2025, volume 15604 of
    Lecture Notes in Computer Science, pages 93–122, Cham, April 2025. Springer Nature Switzerland.
    doi:10.1007/978-3-031-91134-7_4.

13. William Ewald. The Emergence of First-Order Logic. In Edward N. Zalta, editor, The Stanford
    Encyclopedia of Philosophy. Metaphysics Research Lab, Stanford University, spring 2019 edition,
    2019. URL: https://plato.stanford.edu/archives/spr2019/entries/logic-firstorder-emergence/.

14. Murdoch J. Gabbay. Arithmetisation of computation via polynomial semantics for first-order
    logic. Cryptology ePrint Archive, Paper 2024/954, 2024. URL: https://eprint.iacr.org/2024/954.

15. Murdoch J. Gabbay. Arithmetising logic: Polynomial semantics of FOL. Journal of Applied
    Logics—IfCoLog Journal of Logics and their Applications, 12(6):1479–1546, October 2025. URL:
    https://www.collegepublications.co.uk/ifcolog/?00074.

16. Ariel Gabizon, Zachary J. Williamson, and Oana Ciobotaru. PLONK: Permutations over
    Lagrange-bases for oecumenical noninteractive arguments of knowledge. Cryptology ePrint Archive,
    Paper 2019/953, 2019. URL: https://eprint.iacr.org/2019/953.

17. Chaya Ganesh, Anca Nitulescu, and Eduardo Soria-Vazquez. Rinocchio: SNARKs for ring arithmetic.
    Journal of Cryptology, 36(4):41, October 2023. doi:10.1007/s00145-023-09481-3.

18. Albert Garreta, Hendrik Waldner, Ilia Vlasov, Katerina Hristova, Luca Dall’Ava, Marko Čupić, and
    Matthew Klein. Zinc: Succinct arguments with small arithmetization overheads from IOPs of
    proximity to the integers. In Yael Tauman Kalai and Seny F. Kamara, editors, Advances in
    Cryptology – CRYPTO 2025, volume 16006 of Lecture Notes in Computer Science, pages 259–291.
    Springer, Cham, 2025. doi:10.1007/978-3-032-01907-3_9.

19. Alexander Golovnev, Jonathan Lee, Srinath Setty, Justin Thaler, and Riad S. Wahby. Brakedown:
    Linear-time and field-agnostic SNARKs for R1CS. In Helena Handschuh and Anna Lysyanskaya,
    editors, Advances in Cryptology – CRYPTO 2023, volume 14082 of Lecture Notes in Computer
    Science, pages 193–226, Cham, 2023. Springer Nature Switzerland.
    doi:10.1007/978-3-031-38545-2_7.

20. Jens Groth. On the size of pairing-based non-interactive arguments. In Marc Fischlin and
    Jean-Sébastien Coron, editors, Advances in Cryptology – EUROCRYPT 2016, volume 9666 of Lecture
    Notes in Computer Science, pages 305–326, Berlin, Heidelberg, April 2016. Springer Berlin
    Heidelberg. doi:10.1007/978-3-662-49896-5_11.

21. Kunming Jiang, Devora Chait-Roth, Zachary DeStefano, Michael Walfish, and Thomas Wies. Less is
    more: refinement proofs for probabilistic proofs. In 2023 IEEE Symposium on Security and Privacy
    (SP), pages 1112–1129. IEEE, 2023. doi:10.1109/SP46215.2023.10179393.

22. Junkai Liang, Daqi Hu, Pengfei Wu, Yunbo Yang, Qingni Shen, and Zhonghai Wu. SoK: Understanding
    zk-SNARKs: The gap between research and practice. In 34th USENIX Security Symposium (USENIX
    Security 25), pages 2085–2104, Seattle, WA, August 2025. USENIX Association. URL:
    https://www.usenix.org/conference/usenixsecurity25/presentation/liang-sok.

23. Jürgen Nicklisch-Franken and Ruslan Feizerakhmanov. Massimult: A novel parallel CPU architecture
    based on combinator reduction, 2024. arXiv:2412.02765, doi:10.48550/arXiv.2412.02765.

24. Anca Nitulescu. zk-SNARKs: A gentle introduction, 2020. URL:
    https://www.di.ens.fr/~nitulesc/files/Survey-SNARKs.pdf.

25. Michele Orrù, George Kadianakis, Mary Maller, and Greg Zaverucha. Beyond the circuit: How to
    minimize foreign arithmetic in ZKP circuits. IACR Communications in Cryptology, 2(1), April
    2025. doi:10.62056/an-4c3c2h.

26. Bryan Parno, Jon Howell, Craig Gentry, and Mariana Raykova. Pinocchio: Nearly practical
    verifiable computation. In 2013 IEEE Symposium on Security and Privacy, pages 238–252. IEEE, May
    2013. doi:10.1109/SP.2013.47.

27. Srinath Setty, Justin Thaler, and Riad Wahby. Customizable constraint systems for succinct
    arguments. Cryptology ePrint Archive, Paper 2023/552, 2023. URL:
    https://eprint.iacr.org/2023/552.

28. Justin Thaler. Proofs, arguments, and Zero-Knowledge. Foundations and Trends in Privacy and
    Security, 4(2–4):117–660, December 2022. doi:10.1561/3300000030.

29. Urbit Systems Technical Journal. Nock 4K, 2018. Accessed 28 September 2026. URL:
    https://nock.is/content/history/nock-4k/.

30. Riad S. Wahby, Ioanna Tzialla, abhi shelat, Justin Thaler, and Michael Walfish. Doubly-efficient
    zkSNARKs without trusted setup. In 2018 IEEE Symposium on Security and Privacy (SP), pages
    926–943. IEEE, May 2018. doi:10.1109/SP.2018.00060.

31. Yuanju Wei, Xinxuan Zhang, and Yi Deng. Transparent SNARKs over Galois rings. In Tibor Jager and
    Jiaxin Pan, editors, Public-Key Cryptography – PKC 2025, volume 15674 of Lecture Notes in
    Computer Science, pages 418–451, Cham, 2025. Springer Nature Switzerland.
    doi:10.1007/978-3-031-91820-9_14.

32. Zhuo Wu, Xinxuan Zhang, Yi Deng, Yuanju Wei, Zhongliang Zhang, and Liuyu Yang. Polylogarithmic
    polynomial commitment scheme over Galois rings. In Vincent Nicomette, Abdelmalek Benzekri, Nora
    Boulahia-Cuppens, and Jaideep Vaidya, editors, Computer Security – ESORICS 2025, volume 16054 of
    Lecture Notes in Computer Science, pages 400–420, Cham, 2026. Springer Nature Switzerland.
    doi:10.1007/978-3-032-07891-9_21.

33. Hadas Zeilberger, Binyi Chen, and Ben Fisch. BaseFold: Efficient field-agnostic polynomial
    commitment schemes from foldable codes. In Leonid Reyzin and Douglas Stebila, editors, Advances
    in Cryptology – CRYPTO 2024, volume 14929 of Lecture Notes in Computer Science, pages 138–169,
    Cham, 2024. Springer Nature Switzerland. doi:10.1007/978-3-031-68403-6_5.


A  On Lookup Relations

Lookup relations

                   ⎧ gp = (1, 0, 1, log n_a + log n_t, ∂),
                   ⎪ 𝐢 = (⟦t⟧),
                   ⎪ 𝐱 = (⟦a⟧),
                   ⎪ 𝐰 = (a(𝐗)),
Look_{gp,ℛ} = {(𝐢, 𝐱, 𝐰) | a(𝐗) ∈ ℛ_∂^{!!}[𝐗], 𝐗 = (X₁, . . . , X_log n_a),
                   ⎪ t(𝐘) ∈ ℛ_∂^{!!}[𝐘], 𝐘 = (Y₁, . . . , Y_log n_t),
                   ⎩ {a(𝐱) | 𝐱 ∈ {0, 1}^(log n_a)} ⊆ {t(𝐲) | 𝐲 ∈ {0, 1}^(log n_t)}}

are defined as AIRs as follows:

Let a(𝐗) and t(𝐘) be multilinear polynomials on log n_a and log n_t variables respectively, and let
𝐚 and 𝐭 be the vectors of evaluations of a(𝐗) and t(𝐘) on the hypercubes 𝐚 = (a(𝐗))_{{0,1}^{n_a}}
and 𝐭 = (t(𝐘))_{{0,1}^{n_t}}, respectively. Define variables

    𝐖 = ((W_𝐱)_{𝐱∈{0,1}^(log n_a)}, (W_𝐲)_{𝐲∈{0,1}^(log n_t)})

and polynomials

    𝒬_Look = {Q_𝐱(𝐖) :=        ∏        (W_𝐱 − W_𝐲) | 𝐱 ∈ {0, 1}^(log n_a)}.
                           𝐲∈{0,1}^(log n_t)

Then

                          ⎧ gp = (1, 0, 1, log n_a + log n_t, ∂),
                          ⎪ 𝐢 = ([t]),  𝐱 = ([a]),
                          ⎪ a(𝐗) ∈ ℛ_∂^{!!}[𝐗], 𝐗 = (X₁, . . . , X_log n_a),
REL_{gp,ℛ,𝒬_Look} = {(𝐢, 𝐱, 𝐰) | t(𝐘) ∈ ℛ_∂^{!!}[𝐘], 𝐘 = (Y₁, . . . , Y_log n_t),
                          ⎪ 𝐰 = (a(𝐗)),
                          ⎩ Q_𝐱(𝐚, 𝐭) = 0, for all 𝐱 ∈ {0, 1}^(log n_a)}             (2)

is equivalent to the (standard) lookup relation Look_gp [18, Section 4.4].


B  Proof of Theorem 19

Proof. We reason as follows ([15, Theorem 2.4.4] has an analogous proof):

1. It is a fact that 0 = 0 and 1 ≠ 0.
2. It is a fact that x = x′ if and only if (x − x′)² = 0.
3. By non-negativity (Lemma 17).
4. The product of two non-negative numbers is non-zero if and only if they both are.
5. It is a fact that 0 = 0.
6. By construction: range checks compile to 0 and 1 (depending on values of the indicator function
   δ). Their sum is zero if and only if all summands are zero.
7. As for the previous item. ◀


C  Proof of Corollary 32

For the reader’s benefit, we recall the meaning of each parameter contained in the global parameters
gp = (k, m, n, μ, ∂): k is the number of multilinear polynomials f_i comprising the witness; m is
the rank of the auxiliary data 𝐲 in the instance; n is the number of indexing multilinear
polynomials g_i in 𝐢; μ is the dimension of the hypercube onto which the f_i and g_i interpolate;
and ∂ is the bit-length bound on the coefficients of the instance-witness data.

Proof. As in Lemma 30 we transform the instance ((ϕ, R), ς) ∈ REL^EP_gp into an equivalent instance
(𝐱, 𝐰) ∈ REL_{gp,𝒬} which is a valid input to Zinc-PIOP, for some parameters

    gp = (k, m, n, μ, ∂).

The claim concerning the soundness error follows from running a SNARK compiled from Zinc-PIOP and
Zip. To conclude, it suffices to compute gp.

Let (((mkQ^x_ℱ⟨ϕ⟩)_{x∈[len(ς(C))]}, R), (f̃^i_{ς(C)})_{i∈[ar(C)]}) ∈ REL^MV_{gp,ℱ} be obtained from the
FOL instance ((ϕ, R), ς). Following the proof of Lemma 30, we convert these data into an AIR for
Zinc. We obtain one instance-witness pair by considering (mkQ^x_ℱ⟨ϕ⟩)_{x∈[len(ς(C))]} and another by
considering the range checks R; by relabelling indices and defining 𝒬, 𝐢, 𝐱, and 𝐰 appropriately we
can combine these two instances into a single Zinc input relation tuple. Here, however, we
(equivalently) consider the two relations side by side, for clarity.

First consider REL_{gp′,𝒬′} where

    𝒬′ := ((mkQ^x_ℱ⟨ϕ⟩)_{x∈[len(ς(C))]}, x₁(x₁ − 1), …, x_μ(x_μ − 1)),

and 𝐱 = ([f̃^1_{ς(C)}], …, [f̃^{ar(C)}_{ς(C)}]), and 𝐰 = (f̃^1_{ς(C)}, …, f̃^{ar(C)}_{ς(C)}). Here

    gp′ = (ar(C), 0, 0, μ, ∂)

Next, consider the instances of REL_{gp″,𝒬_Look} (cf. equation (2)) corresponding to R; any single
range check R_i ∈ R has global parameters

    gp_i″ = (1, 0, 1, log n_a + log n_t, ∂)

for some n_a, n_t. We next compute log n_a and log n_t.

Recall log n_a is the number of variables on which the multilinear extension comprising the range
check witness 𝐰 = a(𝐗) is defined. Since range checks in R are range checks on the rows of ς(C), we
may take a(𝐗) = f̃^i_{ς(C)} for some i ∈ [ar(C)] and so each range check in R comprises at most
len(ς(C)) integer range checks. Then n_a may be taken to be the minimal integer satisfying ⌈log n_a⌉
= maxbl = μ. By padding appropriately we take log n_a = μ.

Recall t(𝐘) is the multilinear extension interpolating the set in which the evaluations of a(𝐗)
should lie. Since range checks in our semantics arise to ensure pointers are well-defined, range
checks ensure that the entries of rows of ς(C) lie in [len(ς(C))]. Thus log n_t = μ also.

Finally, since R may contain many range checks, we find that the parameters to perform all the range
checks in R are

    gp″ = (|R|, 0, 1, (|R| + 1)μ, ∂)

To compute the final parameters gp = (k, m, n, μ, ∂) of our AIR instance, we note that since the
range checks are performed on the same witness data as in the REL_{gp′,𝒬′} instance, we have k =
ar(C). Moreover, the same choice of t(𝐘) can be used for each range check, so n = 1. Thus the final
parameters of the AIR instance are

    gp = (ar(C), 0, 1, (|R| + 2)μ, ∂)  ◀


D  Two Examples of Arithmetisation in Action

Here we provide concrete examples of sample FOL predicates mapping to instance-witness input pairs
for our SNARK. These examples are selected for their illustrative value, not for displaying the
compactness nor the efficiency of our transform from FOL to SNARK inputs. The latter task of
optimising our transform is primarily an engineering challenge, whereas here we are concerned with
the theoretical and conceptual aspects of our work.

Arithmetising power functions

A common use of SNARKs sees a prover convince a verifier that the prover has computed the output of
some function. We now show how a prover can prove knowledge of values of a function expressed in
FOL. We consider power functions:

▶ Definition 35. The standard inductive definition of aᵇ for a, b ∈ ℕ is a function pow(x, y)
  satisfying:

    base case       pow(a, 0) = 1
    inductive step  pow(a, b + 1) = a ∗ pow(a, b)

This may be written in first-order logic as

    ∀a.(pow(a, 0) = 1) ∧ ∀a, b.(pow(a, b + 1) = a ∗ pow(a, b)),

We define the corresponding predicate expressed via enriched polynomials below, where ϕ_pow is the
validity predicate giving the condition that pow is an arity 4 matrix variable symbol with rows powᵢ
which encode the power function, and where powᵢ(X) denotes an enriched polynomial. We let the
entries of pow₁ correspond to bases, pow₂ correspond to exponents, pow₃ correspond to the function
output, and pow₄ correspond to pointers. Set

    baseCase(X) = (pow₂(X) =̲ 0) ∧̲ (pow₃(X) =̲ 1),

     indStep(X) = pow₁(X) =̲ pow₁(pow₄(X)) ∧̲
                  pow₂(X) =̲ pow₂(pow₄(X)) +̲ 1 ∧̲
                  pow₃(X) =̲ pow₁(X) ∗̲ pow₃(pow₄(X))

Then — using a chained-≤̲ shorthand for range checks — set

    (ϕ_pow, R_pow) = (baseCase(X) ∨̲ indStep(X), 1 ≤̲ pow₄ ≤̲ len(pow))

See [15, Lemma 3.2.6] for a proof that (ϕ_pow, R_pow) does indeed encode Definition 35. We therefore
consider instances of the relation

    Rel^FOL_gp = { ((ϕ, R), ς) | ϕ = ϕ_pow, R = R_pow, C = pow;
                                  ς(C) ∈ 𝓜_{4×len(ς(C))}(ℕ), C ⊨_ς ϕ; R }

Applying the transform of Figure 2 to ϕ_pow, we obtain an enriched polynomial instance in

    Rel^EP_gp = { ((⟨ϕ⟩, R), ς) | ϕ = ϕ_pow, R = R_pow, C = pow;
                                    ς(C) ∈ 𝓜_{4×len(ς(C))}(ℕ), C ⊨_ς ϕ; R }

where

    ⟨ϕ_pow⟩ = (pow₂(X)² + (pow₃(X) − 1)²) ∗
               ((pow₁(X) − pow₁(pow₄(X)))²
                + (pow₂(X) − (pow₂(pow₄(X)) + 1))²
                + (pow₃(X) − pow₁(X) ∗ pow₃(pow₄(X)))²)

We then apply mkQ^x_ℱ with ℱ = {(f̃^i_{ς(pow)})_{i∈[4]}} to obtain an instance in

    REL^MV_{gp,ℱ} = { (((mkQ^x_ℱ⟨ϕ⟩)_{x∈[len(ς(C))]}, R), (f̃^i_{ς(C)})_{i∈[4]}) |
                     ϕ = ϕ_pow, R = R_pow, C = pow;
                     ς(C) ∈ 𝓜_{4×len(ς(C))}(ℕ), C ⊨_ς R;
                     ∀x∈[len(ς(C))](β_ℱ(mkQ^x_ℱ⟨ϕ⟩) = 0) }

By Figure 4 the instance polynomials have the form

    mkQ^x_ℱ⟨ϕ_pow⟩
      = (mkQ^x_ℱ(pow₂(X))² + (mkQ^x_ℱ(pow₃(X)) − 1)²) ∗
          ((mkQ^x_ℱ(pow₁(X)) − mkQ^x_ℱ(pow₁(pow₄(X))))²
           + (mkQ^x_ℱ(pow₂(X)) − (mkQ^x_ℱ(pow₂(pow₄(X))) + 1))²
           + (mkQ^x_ℱ(pow₃(X)) − mkQ^x_ℱ(pow₁(X)) ∗ mkQ^x_ℱ(pow₃(pow₄(X))))²)

      = (b2int(B^{0,x}_{2,1}, …, B^{0,x}_{2,μ})²
         + (b2int(B^{0,x}_{3,1}, …, B^{0,x}_{3,μ}) − 1)²) ∗
          ((b2int(B^{0,x}_{1,1}, …, B^{0,x}_{1,μ})
             − b2int(B^{4,x}_{1,1}, …, B^{4,x}_{1,μ}))²
           + (b2int(B^{0,x}_{2,1}, …, B^{0,x}_{2,μ})
              − (b2int(B^{4,x}_{2,1}, …, B^{4,x}_{2,μ}) + 1))²
           + (b2int(B^{0,x}_{3,1}, …, B^{0,x}_{3,μ})
              − b2int(B^{0,x}_{1,1}, …, B^{0,x}_{1,μ})
                ∗ b2int(B^{4,x}_{3,1}, …, B^{4,x}_{3,μ}))²)

The condition β_ℱ(mkQ^x_ℱ⟨ϕ_pow⟩) = 0 is equivalent to saying that when β_ℱ replaces the
B^{0,x}_{i,ν} with π_ν ∅_b f̃^i_{ς(pow)}(∅_b x) and the B^{4,x}_{i,ν} with π_ν ∅_b f̃^i_{ς(pow)}(∅_b
f̃^4_{ς(pow)}(∅_b x)), that is when β_ℱ replaces the B^{0,x}_{i,ν} with π_ν ∅_b ς(pow)@_{i,x} and the
B^{4,x}_{i,ν} with π_ν ∅_b ς(pow)@_{i,ς(pow)@_{4,x}}, we obtain 0. Thus mkQ^x_ℱ⟨ϕ_pow⟩ has roots at
the binary decompositions of (a subset of) the entries of ς(pow), if ς is a valid interpretation.

The final REL_{gp,𝒬} instance, ignoring range checks for simplicity, has polynomial constraints 𝒬 =
(mkQ^x_ℱ⟨ϕ_pow⟩)_{x∈[len(ς(pow))]} and witness 𝐰 = (f̃^i_{ς(C)})_{i∈[4]}.

Arithmetising SK Combinator reduction

We next consider SNARKs for SK combinator reduction, a Turing-complete system of computation. This
allows us to take as an instance any Turing-complete computation, compiled to SK combinator
calculus, and run a SNARK on the statement expressed in our FOL semantics to allow a prover to prove
knowledge of witnesses to properties of such computations.

The interested reader can find more on SK combinator reduction in [15, Section 3.9]. A nice summary
of the benefits of combinator reduction, and how it relates to other computational models, is
contained in the early pages of [23]; see also [11]. Furthermore a SNARK-friendly treatment of SK
combinators is the proposed EDEN system [1]. [fn 12]

[fn 12] To our knowledge [1] is not a peer-reviewed publication. However, if it is correct it is a
        developed and practical SNARK-friendly treatment of SK combinators (represented as Dyck
        words injected into strings of finite field elements). We quote the authors on why this
        matters: “Most zkVMs emulate the von Neumann architecture and must prove relations between a
        program’s execution and its use of Random Access Memory. However, there are conceptually
        simpler models of computation that are naturally modelled in a SNARK yet are still practical
        for use.” Amen. With respect to that paper, our ‘zkVM’ is FOL itself, and in this section we
        show a simple but direct and effective way to encode SK combinator reduction within it.

We begin by defining the Cantor pairing function:

▶ Definition 36. Define a Cantor pairing map [fn 13]

    ⟨·, ·⟩′ : ℕ × ℕ → ℕ
    ⟨x, y⟩′ = (x + y) ∗ (x + y + 1) + 2 ∗ x

[fn 13] The Cantor pairing function bijects ℕ × ℕ with ℕ and is equal to ⟨x, y⟩′/2. But this would
        require us to include fractions in our term language, which is a wrinkle which we prefer to
        avoid for simplicity, since here we just need some injection that can be expressed as a
        polynomial.

We now arithmetise SK combinator reduction. We first define a relation, where ϕ_SK is a validity
predicate and SK is a matrix variable symbol encoding combinator reduction:

    Rel^FOL_gp = { ((ϕ, R), ς) | ϕ = ϕ_SK, R = R_SK, C = SK;
                                  ς(C) ∈ 𝓜_{ar(C)×len(ς(C))}(ℕ), C ⊨_ς ϕ; R }

where SK has arity 8 with rows SKᵢ and ϕ_SK is defined as follows, where SKᵢ(X) denotes an enriched
polynomial and ⟨·, ·⟩ := ⟨·, ·⟩′ + 2, where ⟨·, ·⟩′ is Cantor pairing. Set

     Kred(X) = SK₁(X) =̲ ⟨⟨1, SK₂(X)⟩, SK₄(X)⟩,

     Sred(X) = SK₁(X) =̲ ⟨⟨⟨0, SK₃(X)⟩, SK₄(X)⟩, SK₅(X)⟩ ∧̲
                SK₂(X) =̲ ⟨⟨SK₃(X), SK₅(X)⟩, ⟨SK₄(X), SK₅(X)⟩⟩,

       Id(X) = SK₁(X) =̲ SK₂(X),

      Par(X) = SK₁(X) =̲ ⟨SK₁(SK₆(X)), SK₁(SK₇(X))⟩ ∧̲
                SK₂(X) =̲ ⟨SK₂(SK₆(X)), SK₂(SK₇(X))⟩ ∧̲
                SK₈(X) =̲ SK₈(SK₆(X)) +̲ 1 ∧̲
                SK₈(X) =̲ SK₈(SK₇(X)) +̲ 1,

     Tran(X) = SK₁(X) =̲ SK₁(SK₆(X)) ∧̲
                SK₂(X) =̲ SK₂(SK₇(X)) ∧̲
                SK₂(SK₆(X)) =̲ SK₁(SK₇(X)) ∧̲
                SK₈(X) =̲ SK₈(SK₆(X)) +̲ 1 ∧̲
                SK₈(X) =̲ SK₈(SK₇(X)) +̲ 1

Then set

    (ϕ_SK, R_SK) = (Kred(X) ∨̲ Sred(X) ∨̲ Id(X) ∨̲ Par(X) ∨̲ Tran(X),
                    1 ≤̲ SK₆ ≤̲ len(SK) ∧̲ 1 ≤̲ SK₇ ≤̲ len(SK))

See [15, Lemma 3.9.10] for a proof that (ϕ_SK, R_SK) does encode SK combinator reduction. Applying
the transform of Figure 2 to ϕ_SK, we obtain an enriched polynomial instance in

    Rel^EP_gp = { ((⟨ϕ⟩, R), ς) | ϕ = ϕ_SK, R = R_SK, C = SK;
                                    ς(C) ∈ 𝓜_{8×len(ς(C))}(ℕ), C ⊨_ς ϕ; R }

where R_SK contains the range checks 1 ≤̲ SK₆ ≤̲ len(SK) and 1 ≤̲ SK₇ ≤̲ len(SK), and

    ⟨ϕ_SK⟩ = (SK₁(X) − ⟨⟨1, SK₂(X)⟩, SK₄(X)⟩)²
              ∗ ((SK₁(X) − ⟨⟨⟨0, SK₃(X)⟩, SK₄(X)⟩, SK₅(X)⟩)²
                 + (SK₂(X) − ⟨⟨SK₃(X), SK₅(X)⟩, ⟨SK₄(X), SK₅(X)⟩⟩)²)
              ∗ (SK₁(X) − SK₂(X))²
              ∗ ((SK₁(X) − ⟨SK₁(SK₆(X)), SK₁(SK₇(X))⟩)²
                 + (SK₂(X) − ⟨SK₂(SK₆(X)), SK₂(SK₇(X))⟩)²
                 + (SK₈(X) − SK₈(SK₆(X)) − 1)²
                 + (SK₈(X) − SK₈(SK₇(X)) − 1)²)
              ∗ ((SK₁(X) − SK₁(SK₆(X)))²
                 + (SK₂(X) − SK₂(SK₇(X)))²
                 + (SK₂(SK₆(X)) − SK₁(SK₇(X)))²
                 + (SK₈(X) − SK₈(SK₆(X)) − 1)²
                 + (SK₈(X) − SK₈(SK₇(X)) − 1)²)

using the transform of Figure 2.

Applying mkQ^x_ℱ to ⟨ϕ_SK⟩ we obtain the len(ς(SK)) polynomials that (partly) comprise the set 𝒬 for
the instance of the relation upon which Zinc-PIOP may be run.
```
