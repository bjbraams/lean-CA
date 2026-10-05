/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Residue.Meromorphic
public import Mathlib.Analysis.Meromorphic.LogDeriv
public import TauCeti.Analysis.Contour.Residue.LogDeriv

/-!
# Residues of logarithmic derivatives

For a nonzero meromorphic germ the residue of its logarithmic derivative is its
integer order: positive at a zero and negative at a pole. The computation is imported from
the Tau Ceti contributors' `TauCeti.Analysis.Contour.Residue.LogDeriv` through the agreement
`Complex.residue_eq_contour_residue` of the two residue definitions on meromorphic germs.

## Main results

* `AnalyticAt.logDeriv`: The logarithmic derivative of a nonvanishing analytic germ is analytic.
* `Complex.residue_logDeriv_of_order`: The residue of a logarithmic derivative equals the
  integer order of the meromorphic germ.
* `Complex.residue_logDeriv`: The residue of the logarithmic derivative of a nonzero meromorphic
  germ is its order.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace Complex

/-- The logarithmic derivative of a nonvanishing analytic germ is analytic. -/
theorem _root_.AnalyticAt.logDeriv {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hne : f c ≠ 0) : AnalyticAt ℂ (logDeriv f) c :=
  hf.deriv.div hf hne

/-- The residue of a logarithmic derivative equals the integer order of the meromorphic germ.

This transports `TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt` by the Tau Ceti
contributors through `Complex.residue_eq_contour_residue`. -/
theorem residue_logDeriv_of_order {f : ℂ → ℂ} {c : ℂ} {n : ℤ}
    (hf : MeromorphicAt f c) (hn : meromorphicOrderAt f c = n) :
    residue (logDeriv f) c = (n : ℂ) := by
  rw [residue_eq_contour_residue hf.logDeriv,
    TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt hf hn]

/-- The residue of the logarithmic derivative of a nonzero meromorphic germ is its order. -/
theorem residue_logDeriv {f : ℂ → ℂ} {c : ℂ}
    (hf : MeromorphicAt f c) (hne : meromorphicOrderAt f c ≠ ⊤) :
    residue (logDeriv f) c = ((meromorphicOrderAt f c).untop₀ : ℂ) :=
  residue_logDeriv_of_order hf (WithTop.coe_untop₀_of_ne_top hne).symm

end Complex
