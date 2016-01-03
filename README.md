# Proof-relevant pi calculus

This the Agda development accompanying the paper
[Proof-relevant pi calculus]
(http://eptcs.web.cse.unsw.edu.au/paper.cgi?LFMTP15:6), presented at
[LFMTP 2015](http://lfmtp.org/workshops/2015/).

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

* <s>`Everything` module that imports everything, for easy build validation</s>
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

## 0.2 Precise cofinality

Implemented a more specific braiding relation, as described in my PLInG
talk. Decided to drop the cube lemma and related formalisation
(residuals of two-dimensional transitions), because the current approach
to dealing with concurrent extrusions will require some rework to
generalise to the cube setting. Suppose I have a 2D action representing
a pair of extrusion-rendezvous, which is concurrent with a bound output.
If the bound output is an extrusion of the _same_ binder as one of the
extrusion-rendezvous, the residual of the 2D action after the bound
output will not be a pair of extrusion-rendezvous; one or both of the
extrusion-rendezvous will have become a regular rendezvous. For 1D
actions, where extrusion-rendezvous and regular rendezvous are not
distinguished, this is covered by the rule that says that the residual
of a non-bound action after a bound action is non-bound. The precise
braiding approach requires a 2D action that distinguishes between
extrusion-rendezvous and regular rendezvous, but without further
representation of the subtleties of extrusion, there is no longer a
functional relationship between the residual of a 2D action after a 1D
action. Without such a function, it is not easy to define (as a
function) the residual of a 2D transition after a 1D transition, since
the function is used to give its type.

Since the cube lemma is a bit of a struggle with the whole braiding
business (since 0.1 release notes below), it seems more sensible to drop
that and retain the more precise cofinality formulation, which I think
fits better with the rest of the paper. The cube lemma isn't required to
define causal equivalence.

## 0.1 LFMTP final version

Wasted a solid week trying to prove a version of `/-preserves-⌣` for a
symmetric version of the relation. If I redefine ⌣ so it is a congruence
by definition (with a symmetric variant of each rule), then the proof
(essentially the definition of a two-dimensional residual) becomes
enormous (many thousands of LOC) and Agda runs out of memory compiling
even a small portion of it. It might be possible to prove it for the
version of ⌣ explicitly closed under symmetry, which is not a congruence
by definition, but would first need to show that ⌣ is a congruence.
