/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Normalization

/-!
# The Riemann mapping theorem

Every nonempty simply connected proper open subset `U` of the plane admits a biholomorphic
map onto the unit disc, which can be normalized to send a given point `z₀ ∈ U` to `0`
with positive real derivative there.

This file adapts `TauCeti.exists_isNormalizedRiemannMapOn`, by the Tau Ceti contributors,
from `TauCeti.Analysis.Complex.Conformal.RiemannMapping.Normalization`. The imported theorem
supplies the normalized map; the adapter expresses its positive complex derivative as an
explicit positive real number.

## Main results

* `Complex.exists_riemannMap`: the Riemann mapping theorem.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorem VII.4.2.
* T. W. Gamelin, *Complex Analysis*, Section XI.4.
* B. Simon, *Basic Complex Analysis*, Theorem 8.1.1.
-/

public noncomputable section

open Set Metric
open scoped ComplexOrder

namespace Complex

variable {U : Set ℂ} {z₀ : ℂ}

/-- **The Riemann mapping theorem.** A simply connected open proper subset `U` of the plane
is mapped by an injective holomorphic function onto the unit disc, normalized so that a given
point `z₀ ∈ U` goes to `0` with positive real derivative.

This is an adapter to the Tau Ceti contributors' `TauCeti.exists_isNormalizedRiemannMapOn`
in `TauCeti.Analysis.Complex.Conformal.RiemannMapping.Normalization`; its proof is imported.

Related formalizations: Vincent Beffara's RMT4 and Yury Kudryashov's Mathlib PR #33505. See
`CREDITS.md`. -/
theorem exists_riemannMap (hU : IsOpen U) (hUc : IsSimplyConnected U) (hne : U ≠ univ)
    (hz₀ : z₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ InjOn f U ∧ f '' U = ball 0 1 ∧ f z₀ = 0 ∧
      ∃ r : ℝ, 0 < r ∧ deriv f z₀ = r := by
  obtain ⟨f, hf⟩ := TauCeti.exists_isNormalizedRiemannMapOn hU hUc hne hz₀
  refine ⟨f, hf.differentiableOn, hf.injOn, hf.image_eq, hf.map_base,
    (deriv f z₀).re, (Complex.pos_iff.mp hf.deriv_pos).1, ?_⟩
  apply Complex.ext
  · simp
  · simpa using (Complex.pos_iff.mp hf.deriv_pos).2.symm

end Complex

end
