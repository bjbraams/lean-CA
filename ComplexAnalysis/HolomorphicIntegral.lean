/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Holomorphic dependence of interval integrals on a complex parameter

An interval integral whose integrand is jointly continuous and holomorphic in a complex
parameter is holomorphic in that parameter. The proof represents the integrand by Cauchy's
formula on a disc and interchanges the two interval integrals; the resulting Cauchy-type
integral of a continuous boundary function is holomorphic inside the circle.

The same tools give the joint continuity of the divided slope `dslope f` of a holomorphic
function, including on the diagonal, through the segment representation
`dslope f x y = ∫ s in 0..1, f' (x + s (y - x))`.

## Main results

* `intervalIntegral_intervalIntegral_swap_of_continuousOn`: Fubini for continuous integrands on
  a rectangle, stated with interval integrals.
* `continuousOn_intervalIntegral_of_continuousOn`: continuity of a parametric interval integral.
* `differentiableOn_intervalIntegral_of_continuousOn`: holomorphy of a parametric interval
  integral in a complex parameter.
* `continuousOn_dslope_prod_of_differentiableOn`: joint continuity of the divided slope.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Complex MeasureTheory Metric Set Filter
open scoped Topology Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Fubini's theorem for a continuous integrand on a rectangle, with interval integrals. -/
theorem intervalIntegral_intervalIntegral_swap_of_continuousOn
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {G : ℝ → ℝ → E}
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Icc a b ×ˢ Icc c d)) :
    ∫ x in a..b, ∫ y in c..d, G x y = ∫ y in c..d, ∫ x in a..b, G x y := by
  have hint : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hG.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  exact integral_integral_swap hint

omit [CompleteSpace E] in
/-- An interval integral depends continuously on a parameter when the integrand is jointly
continuous on the product of an open parameter set and the integration interval. -/
theorem continuousOn_intervalIntegral_of_continuousOn {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] {U : Set X} (hU : IsOpen U) {a b : ℝ} (hab : a ≤ b)
    {F : X → ℝ → E} (hF : ContinuousOn (fun p : X × ℝ => F p.1 p.2) (U ×ˢ Icc a b)) :
    ContinuousOn (fun x => ∫ t in a..b, F x t) U := by
  let G : X → ℝ → E := fun x t => F x (projIcc a b hab t)
  have hGF : ∀ x, ∫ t in a..b, F x t = ∫ t in a..b, G x t := fun x =>
    intervalIntegral.integral_congr fun t ht => by
      simp only [G, projIcc_of_mem hab (by rwa [uIcc_of_le hab] at ht)]
  simp_rw [hGF]
  rw [continuousOn_iff_continuous_domRestrict]
  have := hU.locallyCompactSpace
  have hG : Continuous (fun p : U × ℝ => G p.1 p.2) := by
    have : (fun p : U × ℝ => G p.1 p.2) = (fun p : X × ℝ => F p.1 p.2) ∘
        (fun p : U × ℝ => ((p.1 : X), (projIcc a b hab p.2 : ℝ))) := rfl
    rw [this]
    exact hF.comp_continuous (by fun_prop) fun p => ⟨p.1.2, (projIcc a b hab p.2).2⟩
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x : U => G x) hG a b

/-- An interval integral of a jointly continuous integrand that is holomorphic in a complex
parameter is holomorphic in that parameter.

A counterpart for compact-domain parameter integrals is formalized in Geoffrey Irving's `ray`
project. See `CREDITS.md`. -/
theorem differentiableOn_intervalIntegral_of_continuousOn {U : Set ℂ} (hU : IsOpen U)
    {a b : ℝ} (hab : a ≤ b) {F : ℂ → ℝ → E}
    (hF : ContinuousOn (fun p : ℂ × ℝ => F p.1 p.2) (U ×ˢ Icc a b))
    (hd : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun z => F z t) U) :
    DifferentiableOn ℂ (fun z => ∫ t in a..b, F z t) U := by
  intro z₀ hz₀
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz₀)
  set g : ℂ → E := fun z => ∫ t in a..b, F z t with hg_def
  have hgc : ContinuousOn g U := continuousOn_intervalIntegral_of_continuousOn hU hab hF
  have hrep : ∀ z ∈ ball z₀ r,
      g z = (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • g ζ := by
    intro z hz
    have hcauchy : ∀ t ∈ Icc a b,
        F z t = (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • F ζ t := by
      intro t ht
      refine (DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (f := fun z => F z t)
        ?_ hz).symm
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z₀ hr.ne']
      exact (hd t ht).mono hball
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => deriv (circleMap z₀ r) p.2 •
          ((circleMap z₀ r p.2 - z)⁻¹ • F (circleMap z₀ r p.2) p.1))
        (Icc a b ×ˢ Icc 0 (2 * π)) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => F (circleMap z₀ r p.2) p.1)
          (Icc a b ×ˢ Icc 0 (2 * π)) := by
        refine hF.comp (f := fun p : ℝ × ℝ => (circleMap z₀ r p.2, p.1)) (by fun_prop) ?_
        rintro ⟨t, θ⟩ ⟨ht, _⟩
        exact ⟨hball (circleMap_mem_closedBall z₀ hr.le θ), ht⟩
      have h2 : ContinuousOn (fun p : ℝ × ℝ => (circleMap z₀ r p.2 - z)⁻¹)
          (Icc a b ×ˢ Icc 0 (2 * π)) := by
        refine ContinuousOn.inv₀ (by fun_prop) ?_
        rintro ⟨t, θ⟩ _
        exact sub_ne_zero.mpr (circleMap_ne_mem_ball hz θ)
      have h3 : Continuous (fun p : ℝ × ℝ => deriv (circleMap z₀ r) p.2) := by
        simp only [deriv_circleMap]
        fun_prop
      exact h3.continuousOn.smul (h2.smul h1)
    calc g z = ∫ t in a..b, (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • F ζ t :=
          intervalIntegral.integral_congr fun t ht =>
            hcauchy t (by rwa [uIcc_of_le hab] at ht)
      _ = (2 * π * I : ℂ)⁻¹ • ∫ t in a..b, ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • F ζ t :=
          intervalIntegral.integral_smul _ _
      _ = (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • g ζ := by
          congr 1
          simp only [circleIntegral, hg_def]
          rw [intervalIntegral_intervalIntegral_swap_of_continuousOn hab Real.two_pi_pos.le
            hcont]
          refine intervalIntegral.integral_congr fun θ _ => ?_
          simp only [intervalIntegral.integral_smul]
  have hint : CircleIntegrable g z₀ r :=
    (hgc.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hr.le
  have hw : z₀ ∉ sphere z₀ |r| := by
    rw [abs_of_pos hr]
    exact fun h => hr.ne (by simpa using h)
  have hderiv := (hasDerivAt_circleIntegral_sub_inv_smul hint hw).const_smul
    ((2 * π * I : ℂ)⁻¹)
  have heq : g =ᶠ[𝓝 z₀] fun z => (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • g ζ := by
    filter_upwards [ball_mem_nhds z₀ hr] with z hz
    exact hrep z hz
  exact ((heq.differentiableAt_iff).mpr hderiv.differentiableAt).differentiableWithinAt

/-- The divided slope of a holomorphic function is jointly continuous in its two points,
including on the diagonal, where it is the derivative. -/
theorem continuousOn_dslope_prod_of_differentiableOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → E}
    (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (U ×ˢ U) := by
  have hderiv : ContinuousOn (deriv f) U := (hf.analyticOnNhd hU).deriv.continuousOn
  intro p hp
  by_cases hne : p.1 = p.2
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p.1 hp.1
    have hseg : ∀ x ∈ ball p.1 r, ∀ y ∈ ball p.1 r, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
        x + (s : ℂ) * (y - x) ∈ ball p.1 r := by
      intro x hx y hy s hs
      have := (convex_ball p.1 r).add_smul_sub_mem hx hy hs
      rwa [Complex.real_smul] at this
    have hrep : EqOn (fun q : ℂ × ℂ => dslope f q.1 q.2)
        (fun q : ℂ × ℂ => ∫ s in (0 : ℝ)..1, deriv f (q.1 + (s : ℂ) * (q.2 - q.1)))
        (ball p.1 r ×ˢ ball p.1 r) := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      dsimp only
      by_cases hxy : y = x
      · subst hxy
        simp [dslope_same]
      · rw [dslope_of_ne _ hxy, slope_def_module]
        have hFTC : ∫ s in (0 : ℝ)..1, (y - x) • deriv f (x + (s : ℂ) * (y - x)) =
            f y - f x := by
          have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
            (f := fun s : ℝ => f (x + (s : ℂ) * (y - x)))
            (f' := fun s : ℝ => (y - x) • deriv f (x + (s : ℂ) * (y - x))) ?_ ?_
          · simpa using h
          · intro s hs
            rw [uIcc_of_le zero_le_one] at hs
            have h1 : HasDerivAt (fun w : ℂ => x + w * (y - x)) (y - x) (s : ℂ) := by
              simpa using ((hasDerivAt_id (s : ℂ)).mul_const (y - x)).const_add x
            have hmem := hball (hseg x hx y hy s hs)
            have h2 := ((hf.differentiableAt (hU.mem_nhds hmem)).hasDerivAt.scomp (s : ℂ) h1)
            simpa only [ofRealCLM_apply, ofReal_one, one_smul, Function.comp_def] using!
              h2.scomp s ofRealCLM.hasDerivAt
          · refine (ContinuousOn.intervalIntegrable ?_)
            rw [uIcc_of_le zero_le_one]
            refine continuousOn_const.smul
              (hderiv.comp (f := fun s : ℝ => x + (s : ℂ) * (y - x)) (by fun_prop) ?_)
            intro s hs
            exact hball (hseg x hx y hy s hs)
        rw [intervalIntegral.integral_smul] at hFTC
        rw [← hFTC, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hxy), one_smul]
    have hcont : ContinuousOn
        (fun q : ℂ × ℂ => ∫ s in (0 : ℝ)..1, deriv f (q.1 + (s : ℂ) * (q.2 - q.1)))
        (ball p.1 r ×ˢ ball p.1 r) := by
      refine continuousOn_intervalIntegral_of_continuousOn (isOpen_ball.prod isOpen_ball)
        zero_le_one ?_
      refine hderiv.comp (f := fun q : (ℂ × ℂ) × ℝ => q.1.1 + (q.2 : ℂ) * (q.1.2 - q.1.1))
        (by fun_prop) ?_
      rintro ⟨⟨x, y⟩, s⟩ ⟨⟨hx, hy⟩, hs⟩
      exact hball (hseg x hx y hy s hs)
    have hmem : p ∈ ball p.1 r ×ˢ ball p.1 r :=
      ⟨mem_ball_self hr, by rw [← hne]; exact mem_ball_self hr⟩
    exact ((hcont.congr hrep).continuousAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hmem)).continuousWithinAt
  · have hev : ∀ᶠ q : ℂ × ℂ in 𝓝 p, q.1 ≠ q.2 :=
      (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hne
    have hc : ContinuousAt (fun q : ℂ × ℂ => (q.2 - q.1)⁻¹ • (f q.2 - f q.1)) p := by
      have hf1 : ContinuousAt f p.1 := hf.continuousOn.continuousAt (hU.mem_nhds hp.1)
      have hf2 : ContinuousAt f p.2 := hf.continuousOn.continuousAt (hU.mem_nhds hp.2)
      refine ContinuousAt.smul ?_ ((hf2.comp continuousAt_snd).sub (hf1.comp continuousAt_fst))
      exact (continuousAt_snd.sub continuousAt_fst).inv₀ (sub_ne_zero.mpr (Ne.symm hne))
    refine (hc.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [hev] with q hq
    rw [dslope_of_ne _ (Ne.symm hq), slope_def_module]

end
