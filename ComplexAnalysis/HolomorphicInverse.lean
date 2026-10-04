/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Injective
public import TauCeti.Analysis.Complex.Conformal.Inverse.Function

/-!
# Inverses of injective holomorphic functions

An injective holomorphic function on an open set `U` is an open map, and its inverse on the
image `f '' U` is holomorphic with derivative `(deriv f a)⁻¹` at `f a`. The ingredients are the
open mapping theorem and the nonvanishing of the derivative of an injective holomorphic
function (`Complex.deriv_ne_zero_of_injOn`). The inverse and its derivative use the imported
proofs of the Tau Ceti contributors in `TauCeti.Analysis.Complex.Conformal.Inverse.Function`.

## Main results

* `Complex.isOpen_image_of_injOn`: the image of `U` is open.
* `Complex.hasDerivAt_invFunOn_of_injOn`, `Complex.differentiableOn_invFunOn_of_injOn`: the
  inverse is holomorphic on the image.
* `Complex.differentiableOn_of_leftInverse`: any left inverse is holomorphic on the image.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorem IV.7.6 and Corollary IV.7.6.
-/

public noncomputable section

open Set Metric Filter Function
open scoped Topology

namespace Complex

variable {U : Set ℂ} {f : ℂ → ℂ}

/-- An injective holomorphic function on an open set is open at every point. -/
theorem nhds_le_map_nhds_of_injOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hi : InjOn f U) {a : ℂ} (ha : a ∈ U) : 𝓝 (f a) ≤ map f (𝓝 a) :=
  (hf.analyticOnNhd hU a ha).eventually_constant_or_nhds_le_map_nhds.resolve_left
    (not_eventually_constant_of_injOn_complex (hU.mem_nhds ha) hi)

/-- The image of an open set under an injective holomorphic function is open. -/
theorem isOpen_image_of_injOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨a, ha, rfl⟩
  exact nhds_le_map_nhds_of_injOn hU hf hi ha (image_mem_map (hU.mem_nhds ha))

/-- The inverse of an injective holomorphic function is continuous on the image.

Uses TauCeti's `DifferentiableOn.invFunOn`. -/
theorem continuousOn_invFunOn_of_injOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hi : InjOn f U) : ContinuousOn (invFunOn f U) (f '' U) :=
  (hf.invFunOn hU hi).continuousOn

/-- The inverse of an injective holomorphic function has derivative `(deriv f a)⁻¹` at `f a`.

Uses `TauCeti.hasDerivAt_invFunOn`. -/
theorem hasDerivAt_invFunOn_of_injOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hi : InjOn f U) {a : ℂ} (ha : a ∈ U) :
    HasDerivAt (invFunOn f U) (deriv f a)⁻¹ (f a) :=
  TauCeti.hasDerivAt_invFunOn hf hU hi ha

/-- The inverse of an injective holomorphic function is holomorphic on the image.

Uses TauCeti's `DifferentiableOn.invFunOn`. -/
theorem differentiableOn_invFunOn_of_injOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hi : InjOn f U) : DifferentiableOn ℂ (invFunOn f U) (f '' U) :=
  hf.invFunOn hU hi

/-- A left inverse of a holomorphic function on an open set is holomorphic on the image. -/
theorem differentiableOn_of_leftInverse (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {g : ℂ → ℂ} (hg : ∀ z ∈ U, g (f z) = z) : DifferentiableOn ℂ g (f '' U) := by
  have hi : InjOn f U := fun a ha b hb h ↦ by rw [← hg a ha, h, hg b hb]
  refine (differentiableOn_invFunOn_of_injOn hU hf hi).congr ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [hg a ha, hi.leftInvOn_invFunOn ha]

end Complex

end
