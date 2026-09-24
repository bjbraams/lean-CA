# Complex analysis of one variable

A Lean 4 formalization of fundamental complex analysis of one variable.
The foundational developments are intended as potential Mathlib contributions.

## Organization

There are three main directories.

- `Topology/`.
General compactness, path, graph, semicontinuity, and Baire-theorem support.

- `Analysis/`.
General normed-space, functional-analysis, Taylor-estimate, and integration support,
including the Gamma integral with a complex Laplace parameter.

- `ComplexAnalysis/`.
Single-variable complex analysis: holomorphic branches, Banach-valued primitives and
Cauchy theory on simply connected open domains, integer-valued curve indices with local
constancy, exterior vanishing and circle normalization; Jordan contours, separation,
Cauchy formulas and exhaustions for injective holomorphic disk images; Laurent theory,
residue calculations, the disk argument principle, Rouché's theorem and Hurwitz's theorems;
Montel compactness, Vitali convergence from an interior accumulation point, and
Casorati–Weierstrass with isolated-singularity classification;
subharmonic functions, planar Cauchy transforms, removability, injectivity,
divided differences with coincident nodes, Newton–Taylor formulas, and repeated segment integrals.
The deformation theory includes Cauchy's theorem for continuous homotopies with
differentiable, integrable boundary paths, index invariance for continuous based
homotopies of `C¹` loops, and continuous logarithm tracking. Moving-endpoint identities
pass to improper limits when the endpoint-track integrals vanish. Uniform tail
bounds and explicit power-decay estimates provide convergence criteria.
Exterior-path support proves escape to infinity and endpoint formulas for exact integrals;
general pullback and improper-integration results live in `Analysis`.

`Analysis` and `Topology` depend only on Mathlib. `ComplexAnalysis` builds on them.
The support libraries extend the corresponding Mathlib namespaces.

Each directory has a matching umbrella module. `LeanCA.lean` imports all three.

## Registry statement

To follow.

### Mathematical scope

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

## Related formalizations and credits

[CREDITS.md](CREDITS.md) acknowledges other Lean developments with overlapping
theorems and records comparisons with open Mathlib pull requests and projects
discussed on Lean Zulip. It distinguishes theorem overlap from evidence of code reuse.
