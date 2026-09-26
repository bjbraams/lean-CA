/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis
public import ToMathlib.Topology

/-!
# Support material intended for Mathlib

General analysis and topology results used by `ComplexAnalysis` that are not specific to
complex analysis of one variable. They are collected here, under module names starting with
`ToMathlib`, to mark them as candidates for Mathlib and to avoid clashes with the module names
of other packages. Declarations use the namespaces of the corresponding Mathlib APIs, so they
would move to Mathlib without renaming. This library depends only on Mathlib.

## Main results

This module re-exports the following developments:

* `ToMathlib.Analysis`: General analysis support.
* `ToMathlib.Topology`: General topology support.
-/
