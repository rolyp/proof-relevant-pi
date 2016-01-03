# Proof-relevant pi calculus

This the Agda development accompanying the paper
[Proof-relevant pi calculus]
(http://eptcs.web.cse.unsw.edu.au/paper.cgi?LFMTP15:6), to be presented
at [LFMTP 2015](http://lfmtp.org/workshops/2015/).

# Build instructions

Compiles with:

* Agda 2.4.2.3
* agda-stdlib-0.9 (with
  [postulates accompanying BUILTINs for sized types removed]
  (https://hackage.haskell.org/package/Agda-2.4.2.3/changelog.txt))
* agda-stdlib-ext library, version
  [0.0.2](https://github.com/rolyp/agda-stdlib-ext/releases/tag/0.0.2)

See the appendix of the accompanying paper for notes on module
structure.

# To do

* `Everything` module that imports everything, for easy build validation
* Reorganise packages relating to cofinality and causal equivalence
* Proof of symmetry for causal equivalence
* Vertical composition of braidings
* Several examples of causal equivalence (trickier than it should be)
* <s>Residuation-preserves-concurrency for *symmetric* version of
  concurrency (also tricky)</s>
* Proof of ⊖-preserves-sym
* <s>Proof of Theorem 3 from paper (cubical transition)</s>
* Tighten connection to paper, e.g. key theorems, naming conventions
* Typeclass for residuals (improve overloading mess somehow, and problem
  with use of Δ as type, constructor and meta-variable)

# Design notes

## 0.1.1 Precise cofinality

## 0.1 LFMTP final version

Wasted a solid week trying to prove a version of `/-preserves-⌣` for a
symmetric version of the relation. If I redefine ⌣ so it is a congruence
by definition (with a symmetric variant of each rule), then the proof
(essentially the definition of a two-dimensional residual) becomes
enormous (many thousands of LOC) and Agda runs out of memory compiling
even a small portion of it. It might be possible to prove it for the
version of ⌣ explicitly closed under symmetry, which is not a congruence
by definition, but would first need to show that ⌣ is a congruence.
