/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Subharmonic.Basic
public import ComplexAnalysis.Subharmonic.Convex
public import ComplexAnalysis.Subharmonic.Majorant
public import ComplexAnalysis.Subharmonic.SmoothCriterion
public import ComplexAnalysis.Subharmonic.Submean

/-!
# Subharmonic functions on planar domains

Local submean inequalities, maximum principles, harmonic polynomial majorants, convex examples,
and the smooth Laplacian criterion. Plurisubharmonic functions are developed separately in SCV.

## Main results

This module re-exports the following developments:

* `ComplexAnalysis.Subharmonic.Basic`: Subharmonic functions of one complex variable.
* `ComplexAnalysis.Subharmonic.Convex`: Subharmonicity of continuous convex functions on planar
  domains.
* `ComplexAnalysis.Subharmonic.Majorant`: Harmonic polynomial majorants and the submean
  inequality.
* `ComplexAnalysis.Subharmonic.SmoothCriterion`: The Laplacian criterion for subharmonicity.
* `ComplexAnalysis.Subharmonic.Submean`: Submean estimates for positive powers of holomorphic
  norms.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/
