/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.LaurentSeries.Annulus
public import ComplexAnalysis.LaurentSeries.Basic
public import ComplexAnalysis.LaurentSeries.Geometry

/-!
# Laurent series of one complex variable

Banach-valued circle coefficients, annular Cauchy formulas, Laurent expansions, and planar
circular geometry. Holomorphic dependence on several parameters is supplied separately by SCV.

## Main results

This module re-exports the following developments:

* `ComplexAnalysis.LaurentSeries.Annulus`: Cauchy's formula on an annulus.
* `ComplexAnalysis.LaurentSeries.Basic`: Circle coefficients for analytic Laurent series.
* `ComplexAnalysis.LaurentSeries.Geometry`: Connected annuli and circular neighborhoods in the
  complex plane.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/
