# Project instructions

## Build topology (do not change)

- Lake root is this directory. This directory is on NFS.
- .lake is a symlink to /export/scratch1/braams/lean-codes-lake on local disk.
- Never replace, delete, or retarget that symlink.
- Never run lake build from a subdirectory as if it were the package root.
- Never copy Mathlib or .lake onto NFS ($HOME).
- Do not “fix” the link because it points outside the repo. That is intentional.
- Do not set `LEAN_PATH`, `LAKE_HOME`, or a custom cache dir unless asked.
- If `.lake` is missing or is no longer a symlink to the path above, stop and ask. Do not repair it.
- After every Lean edit: `lake build` from the Lake root.
- For ordinary builds, use lake build > /tmp/ac-build.log 2>&1; reuse this filename to preserve
  the existing command approval.
- Without LSP/MCP: treat `lake build` output as the only proof-state.
- Do not bump lean-toolchain or Mathlib unless asked.

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

## Proof requirements

- All proofs must be accepted by Lean.
- Do not introduce axioms.
- Do not replace `sorry` with `by exact Classical.choice ...` or other logically equivalent
  escape mechanisms.
- Search Mathlib for existing results before recreating substantial theory.
- Additional lemmas are welcome when they clarify the mathematical structure.
- Preserve theorem statements unless they are false or require missing assumptions.
- If a statement appears false then mark the issue clearly before changing it.
- Pay particular attention to empty, singleton, and nontrivial index types.

## Editing

- Keep changes narrowly related to the requested theorem or proof cluster.
- Preserve unrelated user changes.
- Temporary experiments may go in `Scratch.lean`, but remove that file before finishing unless
  asked to retain it.
- Do not commit changes unless explicitly requested.
- If a new Lean file is created, provide it with a documentation header section.
- If a new Lean statement (definition, theorem, lemma or other) is introduced, provide it with
  a brief docstring.

## Validation

For any lean file `f.lean` that has been changed, run:

    lake env lean f.lean

Also run:

    git diff --check
    rg -n '\bsorry\b' ...

## Completion report

Report:

- which theorems were proved;
- which `sorry`s remain;
- validation commands and their results;
- any changed assumptions;
- any theorem found or suspected to be false.

## Documentation files

Do not create dedicated documentation files or any other Markdown files in subdirectories.
Such files should go into the main project directory at the top level.
This includes Markdown files that provide a review of project updates or that describe
planned work.

Files README.md and STRUCTURE.md and SYNOPSIS.md are intended as public documentation, with
README.md as the entry point for the reader. STRUCTURE.md is for more detailed description
for developers and SYNOPSIS.md is content description for mathematicians.

File REMINDERS.md is intended for private documentation for the owner or other editors.
