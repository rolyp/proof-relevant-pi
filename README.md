Proof-relevant pi calculus
---

Building
---

Compiles with:

* Agda 2.4.2.3
* agda-stdlib-0.9 (with
  [postulates accompanying BUILTINs for sized types removed]
  (https://hackage.haskell.org/package/Agda-2.4.2.3/changelog.txt))
* [agda-stdlib-ext](https://github.com/rolyp/agda-stdlib-ext/releases/tag/0.0.2) library

See the appendix of the accompanying paper for notes on module
structure.

To do
---

* Move any design discussions from Research/Impl/README.md to new README.md
* Reorganise packages relating to cofinality and causal equivalence
* Proof of symmetry for causal equivalence
* Vertical composition of braidings
* Several examples of causal equivalence (trickier than it should be)
* Residuation-preserves-concurrency for *symmetric* version of concurrency
* Proof of Theorem 3 (cubical transition)
* Tighten connection to paper, e.g. key theorems, naming conventions
* Should a braiding be determined by a pair of composable actions, or
  simply by an element of 3?
* Typeclass for residuals (improve overloading mess somehow)
