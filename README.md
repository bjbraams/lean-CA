# Complex analysis of one variable

A Lean 4 formalization of fundamental complex analysis of one variable. The project builds on
Mathlib and is written as a potential Mathlib contribution.

## Organization

There are three main directories.

- `Analysis/`.
Spaces of holomorphic maps, shared normal-family arguments, curve integration of exact
one-forms, compactly supported integration, and Taylor-remainder estimates.

- `Topology/`.
Gluing of locally constant differences, frontier lemmas, and semicontinuity support.

- `ComplexAnalysis/`.
Single-variable complex analysis: holomorphic branches, Banach-valued primitives and
Cauchy theory on simply connected open domains, integer-valued curve indices with local
constancy, exterior vanishing and circle normalization; Jordan contours, separation,
Cauchy formulas and exhaustions for injective holomorphic disk images; Laurent theory,
residue calculations, the disk argument principle, Rouché's theorem and Hurwitz's theorems;
Montel compactness, Vitali convergence from an interior accumulation point, and
Casorati–Weierstrass with isolated-singularity classification;
subharmonic functions, planar Cauchy transforms, removability, and injectivity.
The deformation theory includes Cauchy's theorem for continuous homotopies with
differentiable, integrable boundary paths, index invariance for continuous based
homotopies of `C¹` loops, and continuous logarithm tracking. Moving-endpoint identities
pass to improper limits when the endpoint-track integrals vanish.
Exterior-path support proves escape to infinity and endpoint formulas for exact integrals;
general pullback and improper-integration results live in `Analysis`.

`Analysis` and `Topology` depend only on Mathlib. `ComplexAnalysis` builds on them.
The support libraries extend the corresponding Mathlib namespaces.

Each directory has a matching umbrella module. `LeanCA.lean` imports all three.

The file [STRUCTURE.md](STRUCTURE.md) provides a more detailed description of the project
organization. It is written for potential future developers.

## Development process, AI disclosure

The author/developer selected textbook sources for the material to be covered; see
`References` below. From there on all development was done in interaction with AI/LLM
operating as agents; primarily recent instances of GPT and Claude, and also Grok.
General instructions to the AI included to follow Mathlib conventions wherever possible
in matters of generality of statements, namespace choices and naming conventions for
definitions and theorems. All the Lean proofs were done by AI exclusively.

There is a two-stage background to this Lean effort on complex analysis in one variable.
The author started on a project to formalize B. C. Carlson's (1977) approach to special
functions of applied mathematics. This required some results on several complex variables
(SCV) that were not in Mathlib. That inspired a side-project to formalize basic theory of
SCV, but this project in turn needed some results on single variable complex analysis that
were not in Mathlib. That then inspired the present second-level side project.

Here is the [Carlson project](https://github.com/bjbraams/lean-codes).

And here is the [SCV project](https://github.com/bjbraams/lean-SCV).

## Mathematical scope

See [SYNOPSIS.md](SYNOPSIS.md).

## References

* [APP] Agarwal, Perera, Pinelas, *An Introduction to Complex Analysis* (2011), Lectures 25–44.
* [BN] Bak, Newman, *Complex Analysis*, 3rd ed. (2010), Chapters 4–18.
* [Bu] Burckel, *Classical Analysis in the Complex Plane* (2021), Chapters II–VIII.
* [C1] Conway, *Functions of One Complex Variable I* (1978), Chapters IV–XII.
* [C2] Conway, *Functions of One Complex Variable II* (1995), Chapters 13–15, 20, 21.
* [Ga] Gamelin, *Complex Analysis* (2001), Chapters II–VII.
* [He] Heins, *Complex Function Theory* (1968), Chapters IV–VIII.
* [La] Lang, *Complex Analysis*, 4th ed. (1999), Chapters I–XIII.
* [Re] Remmert, *Theory of Complex Functions* (1991), Chapters 6–8.
* [Si] Simon, *A Comprehensive Course in Analysis*, Part 2A (2015), Chapters 2–4.
* [SS] Stein, Shakarchi, *Complex Analysis* (2003), Chapters 2–3.

## Palomar registry statement

To follow.

## Related formalizations and credits

[CREDITS.md](CREDITS.md) acknowledges other Lean developments with overlapping
theorems and records comparisons with open Mathlib pull requests and projects
discussed on Lean Zulip. It distinguishes theorem overlap from evidence of code reuse.
