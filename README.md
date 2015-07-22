Proof-relevant pi calculus
---

This the Agda development accompanying the paper ***Proof-relevant pi
calculus*** (http://eptcs.web.cse.unsw.edu.au/paper.cgi?LFMTP15:6), to
be presented at [LFMTP 2015](http://lfmtp.org/workshops/2015/).

Building
---

Compiles with:

* Agda 2.4.2.3
* agda-stdlib-0.9 (with
  [postulates accompanying BUILTINs for sized types removed]
  (https://hackage.haskell.org/package/Agda-2.4.2.3/changelog.txt))
* agda-stdlib-ext library, version [0.0.2](https://github.com/rolyp/agda-stdlib-ext/releases/tag/0.0.2)

See the appendix of the accompanying paper for notes on module
structure.

To do
---

* Move any design discussions from my research notes to this file
* Reorganise packages relating to cofinality and causal equivalence
* Proof of symmetry for causal equivalence
* Vertical composition of braidings
* Several examples of causal equivalence (trickier than it should be)
* Residuation-preserves-concurrency for *symmetric* version of concurrency (also tricky)
* Proof of Theorem 3 from paper (cubical transition)
* Tighten connection to paper, e.g. key theorems, naming conventions
* Should a braiding be determined by a pair of composable actions, or
  simply by an element of 3?
* Typeclass for residuals (improve overloading mess somehow)
