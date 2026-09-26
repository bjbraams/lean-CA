/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Analysis.Integral.CurveIntegral.Map
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Endpoint formulas for improper integrals of exact one-forms

An exact one-form pulled back along a parametrized curve integrates to the
difference of the limiting potential values. The curve need not have a finite
endpoint: only the potential along it must converge. We treat both a half-line
and an open finite parameter interval. Absolute integrability of the pullback
is explicit; no conditionally convergent integral is identified with a Bochner integral.
We also give limits of finite curve integrals, which only require convergence of
the endpoint potential values, and identify integrable half-line pullbacks with
limits of their finite path integrals.

## Main results

* `integral_Ioi_eq_sub_of_hasFDerivAt`: The integral of an exact form along a half-line
  parametrization is determined by the finite endpoint and the limiting potential at infinity.
* `integral_eq_sub_of_hasFDerivAt_of_tendsto`: An exact form on an open parameter interval
  integrates to the difference of the limiting potential values, even if the curve itself has no
  finite endpoints.
* `tendsto_curveIntegral_of_hasFDerivAt`: Limits of finite integrals of an exact form depend
  only on the limiting endpoint potential values. The endpoints themselves need not converge in
  the ambient space.
* `tendsto_curveIntegral_map_segment`: An integrable half-line pullback is the limit of the
  corresponding finite curve integrals. No primitive for the form is required.

## References

* `Mathlib.MeasureTheory.Integral.IntegralEqImproper`: formal background used by this module.
-/

public section
open Set Filter MeasureTheory
open scoped Topology
open scoped unitInterval

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
  [CompleteSpace F]
  {U : Set E} {P : E → F} {ω : E → E →L[𝕜] F}
  {γ γ' : ℝ → E} {a b : ℝ} {l l₀ l₁ : F}

/-- The integral of an exact form along a half-line parametrization is determined by the
finite endpoint and the limiting potential at infinity. -/
theorem integral_Ioi_eq_sub_of_hasFDerivAt
    (hP : ∀ z ∈ U, HasFDerivAt P (ω z) z)
    (hγ : ∀ t ∈ Ioi a, HasDerivAt γ (γ' t) t)
    (hcont : ContinuousWithinAt γ (Ici a) a) (hγU : MapsTo γ (Ici a) U)
    (hint : IntegrableOn (fun t ↦ ω (γ t) (γ' t)) (Ioi a))
    (hlim : Tendsto (P ∘ γ) atTop (𝓝 l)) :
    ∫ t in Ioi a, ω (γ t) (γ' t) = l - P (γ a) := by
  apply integral_Ioi_of_hasDerivAt_of_tendsto
    ((hP _ (hγU self_mem_Ici)).continuousAt.comp_continuousWithinAt hcont)
    _ hint hlim
  intro t ht
  exact ((hP _ (hγU (le_of_lt ht))).restrictScalars ℝ).comp_hasDerivAt t (hγ t ht)

/-- An exact form on an open parameter interval integrates to the difference of the
limiting potential values, even if the curve itself has no finite endpoints. -/
theorem integral_eq_sub_of_hasFDerivAt_of_tendsto (hab : a < b)
    (hP : ∀ z ∈ U, HasFDerivAt P (ω z) z)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t) (hγU : MapsTo γ (Ioo a b) U)
    (hint : IntervalIntegrable (fun t ↦ ω (γ t) (γ' t)) volume a b)
    (ha : Tendsto (P ∘ γ) (𝓝[>] a) (𝓝 l₀))
    (hb : Tendsto (P ∘ γ) (𝓝[<] b) (𝓝 l₁)) :
    ∫ t in a..b, ω (γ t) (γ' t) = l₁ - l₀ := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab
    (fun t ht ↦ ((hP _ (hγU ht)).restrictScalars ℝ).comp_hasDerivAt t (hγ t ht))
    hint ha hb

omit [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
/-- Limits of finite integrals of an exact form depend only on the limiting endpoint
potential values. The endpoints themselves need not converge in the ambient space. -/
theorem tendsto_curveIntegral_of_hasFDerivAt
    {α : Type*} {ℱ : Filter α} {x y : α → E} {δ : ∀ i, Path (x i) (y i)}
    (hP : ∀ z ∈ U, HasFDerivAt P (ω z) z)
    (hδ : ∀ i, DifferentiableOn ℝ (δ i).extend I)
    (hδU : ∀ i t, δ i t ∈ U) (hint : ∀ i, CurveIntegrable ω (δ i))
    (hx : Tendsto (P ∘ x) ℱ (𝓝 l₀)) (hy : Tendsto (P ∘ y) ℱ (𝓝 l₁)) :
    Tendsto (fun i ↦ curveIntegral ω (δ i)) ℱ (𝓝 (l₁ - l₀)) :=
  (hy.sub hx).congr (fun i ↦
    (curveIntegral_eq_sub_of_hasFDerivAt hP (hδ i) (hδU i) (hint i)).symm)

/-- An integrable half-line pullback is the limit of the corresponding finite curve integrals.
No primitive for the form is required. -/
theorem tendsto_curveIntegral_map_segment
    {G W α : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {ℱ : Filter α} [ℱ.IsCountablyGenerated]
    {a : ℝ} {b : α → ℝ} {γ γ' : ℝ → G} (ω : G → G →L[ℝ] W)
    (hγ : ∀ i, ∀ t ∈ uIcc a (b i), HasDerivAt γ (γ' t) t)
    (hint : IntegrableOn (fun t ↦ ω (γ t) (γ' t)) (Ioi a)) (hb : Tendsto b ℱ atTop) :
    Tendsto (fun i ↦ curveIntegral ω ((Path.segment a (b i)).map' (fun t ht ↦
      (hγ i t (by
        simpa only [Path.range_segment,
            segment_eq_uIcc] using ht)).continuousAt.continuousWithinAt)))
      ℱ (𝓝 (∫ t in Ioi a, ω (γ t) (γ' t))) := by
  exact (intervalIntegral_tendsto_integral_Ioi a hint hb).congr
    (fun i ↦ (curveIntegral_map_segment (hγ i) ω).symm)
