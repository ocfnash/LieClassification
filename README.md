## The classification of Lie algebras in Lean

This repository exists to track remaining work to add the classification of finite-dimensional, simple Lie algebras over an algebraically closed field of characteristic zero to Mathlib.

The plan is for all work to be PR'd directly to Mathlib. This should thus be mostly a repository of `sorry`s until the classification is complete, at which time this repository can be deleted!

I thus plan only to accept PRs to this repository if they are:
 - Mathlib version bump
 - fixing an error
 - improving its role tracking which parts of the classification are missing (e.g., breaking down larger `sorry`s into smaller ones)
 - an exception (it's bound to be useful to allow a bit of divergence from the ideal outlined above)

### Versions of the classification theorem

The following is a sequence of increasingly strong forms of the classification theorem:
 1. Reduction of the classification of Lie algebras to the classification of root systems (does not require defining the families A, B, ..., G)
 1. Proof that any simple Lie algebras belongs to one of the familes A, B, ..., G
 1. Proof that any simple Lie algebras belongs to one of the familes A, B, ..., G and that no two items in this list coincide (apart from low-rank coincidences)

I propose to aim for the easiest of these goals, and possibly to reassess in due course.
