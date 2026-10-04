/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.DiscMobius
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Derivative

/-!
# The Schwarz–Pick lemma and the hyperbolic metric of the disc

For a holomorphic self-map `f` of the unit disc, the Schwarz–Pick lemma states that `f`
contracts the pseudo-hyperbolic distance `‖discMobius a z‖`, and contracts the corresponding
infinitesimal (derivative) form `‖f' a‖ / (1 - ‖f a‖ ^ 2) ≤ 1 / (1 - ‖a‖ ^ 2)`.

Both forms use the imported proofs of the Tau Ceti contributors in
`TauCeti.Analysis.Complex.Conformal.SchwarzPick.Derivative`, adapted to the local
`discMobius` and Mathlib's `Complex.normSq`.

## Main results

* `Complex.norm_discMobius_apply_apply_le`: **the Schwarz–Pick lemma**, distance form.
* `Complex.norm_deriv_div_one_sub_normSq_le`: **the Schwarz–Pick lemma**, derivative form.

## References

* B. Simon, *Basic Complex Analysis*, Section 7.4.
* T. Gamelin, *Complex Analysis*, Chapter IX, Section 3.
-/

public noncomputable section

open Set Metric Filter ComplexConjugate

namespace Complex

variable {f : ℂ → ℂ}

/-- **The Schwarz–Pick lemma**, distance form. A holomorphic self-map of the disc contracts the
pseudo-hyperbolic distance `‖discMobius a z‖`.

Uses `TauCeti.pseudoHyperbolicExpr_map_le`. -/
theorem norm_discMobius_apply_apply_le (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1)) {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ‖discMobius (f a) (f w)‖ ≤ ‖discMobius a w‖ := by
  simpa only [TauCeti.pseudoHyperbolicExpr_def, Complex.discMobius] using
    TauCeti.pseudoHyperbolicExpr_map_le hf hmaps
      (mem_ball_zero_iff.mpr hw) (mem_ball_zero_iff.mpr ha)

/-- **The Schwarz–Pick lemma**, derivative form. A holomorphic self-map of the disc contracts
the hyperbolic metric infinitesimally.

Uses `TauCeti.norm_deriv_div_one_sub_norm_sq_le`. -/
theorem norm_deriv_div_one_sub_normSq_le (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1)) {a : ℂ} (ha : ‖a‖ < 1) :
    ‖deriv f a‖ / (1 - normSq (f a)) ≤ 1 / (1 - normSq a) := by
  simpa only [Complex.normSq_eq_norm_sq] using
    TauCeti.norm_deriv_div_one_sub_norm_sq_le hf hmaps (mem_ball_zero_iff.mpr ha)

end Complex

end
