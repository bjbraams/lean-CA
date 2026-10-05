# Project instructions — lean-CA

Before working, read and follow [the shared Lean instructions](../lean-codes/AGENTS.common.md),
then apply the project-specific rules below. Resolve that path relative to this file.
Local rules take precedence over the shared defaults. If the shared file is unavailable,
report that fact rather than proceeding without it.

## Build settings

- Lake root: the directory containing this `AGENTS.md`.
- Build output: `.lake/build-CA`; preserve the matching `buildDir` in `lakefile.toml`.
- Ordinary build command: `lake build > /tmp/ac-build.log 2>&1`.

## Project

This is a collection of Lean 4 projects using Mathlib and written with the intent to form a
contribution to Mathlib. The objective (as it has developed over time) is to formalize core
results in complex analysis of one variable, building on Lean Mathlib and following Mathlib
conventions for mathematical generality, namespaces and names. The following references are
a guide to the desired coverage.

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

PDF files of these references are available to the Agent, except for [Si] for which we
have only the ToC in PDF.

The following are concerns to be kept in mind and addressed throughout the development process.
- Are theorems stated in the most general appropriate setting?
- Does the code adhere to Mathlib naming conventions for defs, theorems, lemmas and structures
  both in sentence structure and in capitalization and use of underscores?
- Does every def, theorem, lemma, structure and structure field have a formal docstring and is
  the docstring appropriate?
- Are the Namespaces appropriate?
- Is every file a module? Does each file have a module docstring and does it properly summarize
  the mathematical scope, notation, and main results?
- Can long proofs be simplified or broken up, perhaps with use of helper theorems?

## Dependencies and import layers

Mathlib and TauCeti are allowed in `ToMathlib` and `ComplexAnalysis`.
`ToMathlib` must not import `ComplexAnalysis`; `ComplexAnalysis` may import `ToMathlib`.
When propagating source changes to lean-SCV, check that its dependency configuration
supports new imports. Adding a dependency here does not authorize changing companion
configurations. Follow the master-copy rules below.

## Project-specific editing

- This project is the master copy of the `ComplexAnalysis` files. The companion project
  `../lean-SCV` holds exact copies of the subset it imports, and its `ToMathlib` files that
  share a name with ones here have identical content and path. The umbrella modules
  `ToMathlib.lean`, `ToMathlib/Analysis.lean` and `ToMathlib/Topology.lean` are exempt: each
  project's umbrella imports its own inventory. Changes to a file used there are propagated
  by copying; renaming or removing declarations in such a file requires a matching update in
  lean-SCV.

## Documentation files

Files README.md and STRUCTURE.md and SYNOPSIS.md are intended as public documentation, with
README.md as the entry point for the reader. STRUCTURE.md is for more detailed description
for developers and SYNOPSIS.md is content description for mathematicians.
