/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.DiscMobius
public import ComplexAnalysis.HolomorphicInverse
public import ComplexAnalysis.RiemannMapping
public import Mathlib.Analysis.Complex.Schwarz

/-!
# Automorphisms of the unit disc

Every holomorphic bijection of the unit disc onto itself has the form `z ↦ c * φ_a z` with
`‖c‖ = 1` and `‖a‖ < 1`, where `φ_a` is the disc Möbius transformation
(`Complex.discMobius`). The proof is the Schwarz lemma applied to the map and its inverse
after normalizing the fixed point to `0`. As a consequence the normalized Riemann map is
unique.

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
disc into itself, is a rotation. -/
theorem exists_eqOn_mul_of_leftInverse_of_map_zero {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hfm : MapsTo f (ball 0 1) (ball 0 1)) (hf0 : f 0 = 0)
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hgm : MapsTo g (ball 0 1) (ball 0 1))
    (hgf : ∀ z ∈ ball 0 1, g (f z) = z) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ EqOn f (fun z ↦ c * z) (ball 0 1) := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hg0 : g 0 = 0 := by
    have := hgf 0 h0
    rwa [hf0] at this
  have hfmaps : MapsTo f (ball 0 1) (closedBall (f 0) 1) := by
    rw [hf0]
    exact hfm.mono_right ball_subset_closedBall
  have hgmaps : MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
    rw [hg0]
    exact hgm.mono_right ball_subset_closedBall
  have hf1 : ‖deriv f 0‖ ≤ 1 := norm_deriv_le_one_of_mapsTo_ball hf hfmaps one_pos
  have hg1 : ‖deriv g 0‖ ≤ 1 := norm_deriv_le_one_of_mapsTo_ball hg hgmaps one_pos
  have hchain : deriv g 0 * deriv f 0 = 1 := by
    have hfd : HasDerivAt f (deriv f 0) 0 :=
      (hf.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    have hgd : HasDerivAt g (deriv g 0) (f 0) := by
      rw [hf0]
      exact (hg.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    have hev : (g ∘ f) =ᶠ[𝓝 0] id := by
      filter_upwards [isOpen_ball.mem_nhds h0] with z hz
      exact hgf z hz
    have := ((hgd.comp 0 hfd).congr_of_eventuallyEq hev.symm).deriv
    rw [deriv_id] at this
    exact this.symm
  have hnorm : ‖deriv f 0‖ = 1 := by
    have h1 : ‖deriv g 0‖ * ‖deriv f 0‖ = 1 := by rw [← norm_mul, hchain, norm_one]
    nlinarith [norm_nonneg (deriv f 0), norm_nonneg (deriv g 0)]
  obtain ⟨C, hC, hfeq⟩ := affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div' hf hfmaps
    ⟨0, h0, by rw [dslope_same, hnorm, div_one]⟩
  refine ⟨C, by simpa using hC, fun z hz ↦ ?_⟩
  rw [hfeq hz, hf0]
  simp only [zero_add, sub_zero, smul_eq_mul, mul_comm]

/-- **Automorphisms of the disc.** A holomorphic bijection of the disc with holomorphic inverse
is `z ↦ c * φ_a z` with `‖c‖ = 1` and `‖a‖ < 1`. -/
theorem exists_eqOn_mul_discMobius_of_leftInverse {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hfm : MapsTo f (ball 0 1) (ball 0 1))
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hgm : MapsTo g (ball 0 1) (ball 0 1))
    (hgf : ∀ z ∈ ball 0 1, g (f z) = z) (hfg : ∀ z ∈ ball 0 1, f (g z) = z) :
    ∃ c a : ℂ, ‖c‖ = 1 ∧ ‖a‖ < 1 ∧ EqOn f (fun z ↦ c * discMobius a z) (ball 0 1) := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  set a := g 0
  have ha : ‖a‖ < 1 := mem_ball_zero_iff.mp (hgm h0)
  have hna : ‖-a‖ < 1 := by rwa [norm_neg]
  set F : ℂ → ℂ := fun z ↦ f (discMobius (-a) z)
  set G : ℂ → ℂ := fun z ↦ discMobius a (g z)
  have hFd : DifferentiableOn ℂ F (ball 0 1) :=
    hf.comp (differentiableOn_discMobius_ball hna) (mapsTo_discMobius_ball hna)
  have hFm : MapsTo F (ball 0 1) (ball 0 1) := fun z hz ↦ hfm (mapsTo_discMobius_ball hna hz)
  have hF0 : F 0 = 0 := by
    change f (discMobius (-a) 0) = 0
    rw [discMobius_zero_right, neg_neg]
    exact hfg 0 h0
  have hGd : DifferentiableOn ℂ G (ball 0 1) := (differentiableOn_discMobius_ball ha).comp hg hgm
  have hGm : MapsTo G (ball 0 1) (ball 0 1) := fun z hz ↦ mapsTo_discMobius_ball ha (hgm hz)
  have hGF : ∀ z ∈ ball 0 1, G (F z) = z := by
    intro z hz
    change discMobius a (g (f (discMobius (-a) z))) = z
    rw [hgf _ (mapsTo_discMobius_ball hna hz)]
    have := discMobius_neg_discMobius hna (mem_ball_zero_iff.mp hz).le
    rwa [neg_neg] at this
  obtain ⟨c, hc, hFeq⟩ := exists_eqOn_mul_of_leftInverse_of_map_zero hFd hFm hF0 hGd hGm hGF
  refine ⟨c, a, hc, ha, fun z hz ↦ ?_⟩
  have h1 : f z = F (discMobius a z) := by
    change f z = f (discMobius (-a) (discMobius a z))
    rw [discMobius_neg_discMobius ha (mem_ball_zero_iff.mp hz).le]
  rw [h1, hFeq (mapsTo_discMobius_ball ha hz)]

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
the unit disc sending `z₀` to `0` with positive real derivative there agree on `U`. -/
theorem eqOn_of_riemannMap (hU : IsOpen U) (hz₀ : z₀ ∈ U) {f₁ f₂ : ℂ → ℂ}
    (hf₁ : DifferentiableOn ℂ f₁ U) (hi₁ : InjOn f₁ U) (himg₁ : f₁ '' U = ball 0 1)
    (h₁0 : f₁ z₀ = 0) {r₁ : ℝ} (hr₁ : 0 < r₁) (hd₁ : deriv f₁ z₀ = r₁)
    (hf₂ : DifferentiableOn ℂ f₂ U) (hi₂ : InjOn f₂ U) (himg₂ : f₂ '' U = ball 0 1)
    (h₂0 : f₂ z₀ = 0) {r₂ : ℝ} (hr₂ : 0 < r₂) (hd₂ : deriv f₂ z₀ = r₂) :
    EqOn f₁ f₂ U := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  -- `F = f₂ ∘ f₁⁻¹` is an automorphism of the disc fixing `0`, with inverse `f₁ ∘ f₂⁻¹`
  set g := invFunOn f₁ U
  have hg : DifferentiableOn ℂ g (ball 0 1) :=
    (differentiableOn_invFunOn_of_injOn hU hf₁ hi₁).mono himg₁.symm.subset
  have hgm : MapsTo g (ball 0 1) U := fun w hw ↦ invFunOn_mem (himg₁.symm.subset hw)
  have hfg : ∀ w ∈ ball 0 1, f₁ (g w) = w := fun w hw ↦ invFunOn_eq (himg₁.symm.subset hw)
  have hg0 : g 0 = z₀ := by
    have := hi₁.leftInvOn_invFunOn hz₀
    rwa [h₁0] at this
  set F : ℂ → ℂ := fun w ↦ f₂ (g w)
  have hFd : DifferentiableOn ℂ F (ball 0 1) := hf₂.comp hg hgm
  have hFm : MapsTo F (ball 0 1) (ball 0 1) := fun w hw ↦
    himg₂.subset (mem_image_of_mem f₂ (hgm hw))
  have hF0 : F 0 = 0 := by
    change f₂ (g 0) = 0
    rw [hg0, h₂0]
  set G : ℂ → ℂ := fun w ↦ f₁ (invFunOn f₂ U w)
  have hGd : DifferentiableOn ℂ G (ball 0 1) :=
    hf₁.comp ((differentiableOn_invFunOn_of_injOn hU hf₂ hi₂).mono himg₂.symm.subset)
      fun w hw ↦ invFunOn_mem (himg₂.symm.subset hw)
  have hGm : MapsTo G (ball 0 1) (ball 0 1) := fun w hw ↦
    himg₁.subset (mem_image_of_mem f₁ (invFunOn_mem (himg₂.symm.subset hw)))
  have hGF : ∀ w ∈ ball 0 1, G (F w) = w := by
    intro w hw
    change f₁ (invFunOn f₂ U (f₂ (g w))) = w
    rw [hi₂.leftInvOn_invFunOn (hgm hw), hfg w hw]
  obtain ⟨c, hc, hFeq⟩ := exists_eqOn_mul_of_leftInverse_of_map_zero hFd hFm hF0 hGd hGm hGF
  -- the derivative of `F` at `0` is `c = r₂ / r₁`
  have hderivF : deriv F 0 = c := by
    have hev : F =ᶠ[𝓝 0] fun z ↦ c * z :=
      hFeq.eventuallyEq_of_mem (isOpen_ball.mem_nhds h0)
    have hcz : HasDerivAt (fun z : ℂ ↦ c * z) c 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul c
    rw [hev.deriv_eq, hcz.deriv]
  have hderivF' : deriv F 0 = deriv f₂ z₀ * (deriv f₁ z₀)⁻¹ := by
    have hgd : HasDerivAt g (deriv f₁ z₀)⁻¹ 0 := by
      have := hasDerivAt_invFunOn_of_injOn hU hf₁ hi₁ hz₀
      rwa [h₁0] at this
    have hf₂d : HasDerivAt f₂ (deriv f₂ z₀) (g 0) := by
      rw [hg0]
      exact (hf₂.differentiableAt (hU.mem_nhds hz₀)).hasDerivAt
    exact (hf₂d.comp 0 hgd).deriv
  have hc' : c = ((r₂ / r₁ : ℝ) : ℂ) := by
    rw [← hderivF, hderivF', hd₁, hd₂]
    push_cast
    ring
  have hc1 : c = 1 := by
    have h1 : ‖c‖ = r₂ / r₁ := by
      rw [hc', norm_real, Real.norm_of_nonneg (div_pos hr₂ hr₁).le]
    rw [hc] at h1
    rw [hc', ← h1]
    exact ofReal_one
  -- conclude
  intro z hz
  have hw : f₁ z ∈ ball 0 1 := himg₁.subset (mem_image_of_mem f₁ hz)
  have h1 := hFeq hw
  simp only [hc1, one_mul] at h1
  have hgz : g (f₁ z) = z := hi₁.leftInvOn_invFunOn hz
  calc f₁ z = F (f₁ z) := h1.symm
    _ = f₂ (g (f₁ z)) := rfl
    _ = f₂ z := by rw [hgz]

end Complex

end
