/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.DiscMobius
public import ComplexAnalysis.HolomorphicInverse
public import ComplexAnalysis.RiemannMapping
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Uniqueness
public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Classification
public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Rotation

/-!
# Automorphisms of the unit disc

Every holomorphic bijection of the unit disc onto itself has the form `z ↦ c * φ_a z` with
`‖c‖ = 1` and `‖a‖ < 1`, where `φ_a` is the disc Möbius transformation
(`Complex.discMobius`). As a consequence the normalized Riemann map is unique. The proofs are
imported from the Tau Ceti contributors: the rotation theorem from
`TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Rotation`, the classification from
`TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Classification`, and uniqueness up to
rotation from `TauCeti.Analysis.Complex.Conformal.RiemannMapping.Uniqueness`. The statements here
adapt them to the local Möbius and Riemann-map interfaces.

## Main results

* `Complex.exists_eqOn_mul_of_leftInverse_of_map_zero`: an automorphism fixing `0` is a
  rotation.
* `Complex.exists_eqOn_mul_discMobius_of_leftInverse`,
  `Complex.exists_eqOn_mul_discMobius_of_injOn_of_image_eq`: the classification.
* `Complex.eqOn_of_riemannMap`: uniqueness of the normalized Riemann map.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorem VI.2.5 and VII.4.2.
* T. W. Gamelin, *Complex Analysis*, Section IX.2.
-/

public noncomputable section

open Set Metric Filter Function
open scoped Topology ComplexConjugate

namespace Complex

/-- A holomorphic self-map of the disc fixing `0`, with a holomorphic left inverse mapping the
disc into itself, is a rotation.

Uses `TauCeti.exists_eqOn_const_mul_of_leftInvOn_ball_of_map_zero`. -/
theorem exists_eqOn_mul_of_leftInverse_of_map_zero {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hfm : MapsTo f (ball 0 1) (ball 0 1)) (hf0 : f 0 = 0)
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hgm : MapsTo g (ball 0 1) (ball 0 1))
    (hgf : ∀ z ∈ ball 0 1, g (f z) = z) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ EqOn f (fun z ↦ c * z) (ball 0 1) :=
  TauCeti.exists_eqOn_const_mul_of_leftInvOn_ball_of_map_zero hf hg hfm hgm hgf hf0

/-- **Automorphisms of the disc.** A holomorphic bijection of the disc with holomorphic inverse
is `z ↦ c * φ_a z` with `‖c‖ = 1` and `‖a‖ < 1`.

Uses `TauCeti.exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv`. -/
theorem exists_eqOn_mul_discMobius_of_leftInverse {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hfm : MapsTo f (ball 0 1) (ball 0 1))
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hgm : MapsTo g (ball 0 1) (ball 0 1))
    (hgf : ∀ z ∈ ball 0 1, g (f z) = z) (hfg : ∀ z ∈ ball 0 1, f (g z) = z) :
    ∃ c a : ℂ, ‖c‖ = 1 ∧ ‖a‖ < 1 ∧ EqOn f (fun z ↦ c * discMobius a z) (ball 0 1) := by
  obtain ⟨u, a, -, hu⟩ := TauCeti.exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv
    hf hg hfm hgm hgf hfg
  refine ⟨u, a, by simp, a.norm_lt_one, fun z hz ↦ ?_⟩
  have := hu (UnitDisc.mk z (mem_ball_zero_iff.mp hz))
  rw [TauCeti.coe_unitDiscStandardAutomorphismEquiv_apply, UnitDisc.coe_mk] at this
  exact this

/-- **Automorphisms of the disc.** An injective holomorphic map of the disc onto itself is
`z ↦ c * φ_a z` with `‖c‖ = 1` and `‖a‖ < 1`. -/
theorem exists_eqOn_mul_discMobius_of_injOn_of_image_eq {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (himg : f '' ball 0 1 = ball 0 1) :
    ∃ c a : ℂ, ‖c‖ = 1 ∧ ‖a‖ < 1 ∧ EqOn f (fun z ↦ c * discMobius a z) (ball 0 1) := by
  have hfm : MapsTo f (ball 0 1) (ball 0 1) := fun z hz ↦ himg.subset (mem_image_of_mem f hz)
  have hg : DifferentiableOn ℂ (invFunOn f (ball 0 1)) (ball 0 1) :=
    (differentiableOn_invFunOn_of_injOn isOpen_ball hf hi).mono himg.symm.subset
  have hgm : MapsTo (invFunOn f (ball 0 1)) (ball 0 1) (ball 0 1) := fun w hw ↦
    invFunOn_mem (himg.symm.subset hw)
  have hgf : ∀ z ∈ ball 0 1, invFunOn f (ball 0 1) (f z) = z := fun z hz ↦
    hi.leftInvOn_invFunOn hz
  have hfg : ∀ w ∈ ball 0 1, f (invFunOn f (ball 0 1) w) = w := fun w hw ↦
    invFunOn_eq (himg.symm.subset hw)
  exact exists_eqOn_mul_discMobius_of_leftInverse hf hfm hg hgm hgf hfg

variable {U : Set ℂ} {z₀ : ℂ}

/-- **Uniqueness of the Riemann map.** Two injective holomorphic maps of an open set `U` onto
the unit disc sending `z₀` to `0` with positive real derivative there agree on `U`.

Uses `TauCeti.exists_eqOn_const_mul_of_image_eq_ball_of_apply_eq_zero`. -/
theorem eqOn_of_riemannMap (hU : IsOpen U) (hz₀ : z₀ ∈ U) {f₁ f₂ : ℂ → ℂ}
    (hf₁ : DifferentiableOn ℂ f₁ U) (hi₁ : InjOn f₁ U) (himg₁ : f₁ '' U = ball 0 1)
    (h₁0 : f₁ z₀ = 0) {r₁ : ℝ} (hr₁ : 0 < r₁) (hd₁ : deriv f₁ z₀ = r₁)
    (hf₂ : DifferentiableOn ℂ f₂ U) (hi₂ : InjOn f₂ U) (himg₂ : f₂ '' U = ball 0 1)
    (h₂0 : f₂ z₀ = 0) {r₂ : ℝ} (hr₂ : 0 < r₂) (hd₂ : deriv f₂ z₀ = r₂) :
    EqOn f₁ f₂ U := by
  obtain ⟨u, hu⟩ := TauCeti.exists_eqOn_const_mul_of_image_eq_ball_of_apply_eq_zero hU hf₁ hf₂
    hi₁ hi₂ himg₁ himg₂ hz₀ h₁0 h₂0
  -- the rotation factor is `r₂ / r₁`, a positive real number of norm one
  have hderiv : deriv f₂ z₀ = u * deriv f₁ z₀ := by
    rw [(hu.eventuallyEq_of_mem (hU.mem_nhds hz₀)).deriv_eq, deriv_const_mul _
      (hf₁.differentiableAt (hU.mem_nhds hz₀))]
  rw [hd₁, hd₂] at hderiv
  have hu1 : (u : ℂ) = 1 := by
    have hreal : (u : ℂ) = ((r₂ / r₁ : ℝ) : ℂ) := by
      push_cast
      field_simp [ofReal_ne_zero.mpr hr₁.ne']
      exact hderiv.symm
    have hn : r₂ / r₁ = 1 := by
      have := congrArg norm hreal
      rwa [Circle.norm_coe, norm_real, Real.norm_of_nonneg (div_pos hr₂ hr₁).le, eq_comm] at this
    rw [hreal, hn, ofReal_one]
  intro z hz
  simp [hu hz, hu1]

end Complex

end
