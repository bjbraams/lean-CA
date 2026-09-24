/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Injective

/-!
# Inverses of injective holomorphic functions

An injective holomorphic function on an open set `U` is an open map, and its inverse on the
image `f '' U` is holomorphic with derivative `(deriv f a)⁻¹` at `f a`. The ingredients are the
open mapping theorem and the nonvanishing of the derivative of an injective holomorphic
function (`Complex.deriv_ne_zero_of_injOn`).

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

/-- The inverse of an injective holomorphic function is continuous on the image. -/
theorem continuousOn_invFunOn_of_injOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hi : InjOn f U) : ContinuousOn (invFunOn f U) (f '' U) := by
  rintro _ ⟨a, ha, rfl⟩
  apply ContinuousAt.continuousWithinAt
  have hleft : (invFunOn f U ∘ f) =ᶠ[𝓝 a] id :=
    Filter.mem_of_superset (hU.mem_nhds ha) fun _ hz => hi.leftInvOn_invFunOn hz
  rw [ContinuousAt, hi.leftInvOn_invFunOn ha]
  have ht : Tendsto (invFunOn f U ∘ f) (𝓝 a) (𝓝 a) := tendsto_id.congr' hleft.symm
  change map (invFunOn f U ∘ f) (𝓝 a) ≤ 𝓝 a at ht
  exact (Filter.map_mono (nhds_le_map_nhds_of_injOn hU hf hi ha)).trans (by rwa [map_map])

/-- The inverse of an injective holomorphic function has derivative `(deriv f a)⁻¹` at `f a`. -/
theorem hasDerivAt_invFunOn_of_injOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hi : InjOn f U) {a : ℂ} (ha : a ∈ U) :
    HasDerivAt (invFunOn f U) (deriv f a)⁻¹ (f a) := by
  have himg : f '' U ∈ 𝓝 (f a) :=
    (isOpen_image_of_injOn hU hf hi).mem_nhds (mem_image_of_mem f ha)
  have hcont : ContinuousAt (invFunOn f U) (f a) :=
    (continuousOn_invFunOn_of_injOn hU hf hi).continuousAt himg
  have hd : HasDerivAt f (deriv f a) (invFunOn f U (f a)) := by
    rw [hi.leftInvOn_invFunOn ha]
    exact (hf.differentiableAt (hU.mem_nhds ha)).hasDerivAt
  refine HasDerivAt.of_local_left_inverse hcont hd (deriv_ne_zero_of_injOn hU hf hi ha) ?_
  filter_upwards [himg] with w hw
  exact invFunOn_eq hw

/-- The inverse of an injective holomorphic function is holomorphic on the image. -/
theorem differentiableOn_invFunOn_of_injOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hi : InjOn f U) : DifferentiableOn ℂ (invFunOn f U) (f '' U) := by
  rintro _ ⟨a, ha, rfl⟩
  exact (hasDerivAt_invFunOn_of_injOn hU hf hi ha).differentiableAt.differentiableWithinAt

/-- A left inverse of a holomorphic function on an open set is holomorphic on the image. -/
theorem differentiableOn_of_leftInverse (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {g : ℂ → ℂ} (hg : ∀ z ∈ U, g (f z) = z) : DifferentiableOn ℂ g (f '' U) := by
  have hi : InjOn f U := fun a ha b hb h => by rw [← hg a ha, h, hg b hb]
  refine (differentiableOn_invFunOn_of_injOn hU hf hi).congr ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [hg a ha, hi.leftInvOn_invFunOn ha]

end Complex

end
