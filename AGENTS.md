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
contribution to Mathlib.

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

Files README.md and STRUCTURE.md are intended as public documentation, with README.md as
the entry point for the reader and STRUCTURE.md for more detailed description.

File REMINDERS.md is intended for private documentation for the owner or other editors.
