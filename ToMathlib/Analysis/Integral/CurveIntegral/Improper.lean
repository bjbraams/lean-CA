/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Integral.CurveIntegral.Map
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Limits of curve integrals

Related work on the curve-integral API includes
[Mathlib PR #39524](https://github.com/leanprover-community/mathlib4/pull/39524),
line-segment integrability and the fundamental theorem of calculus by FordUniver, and
[Mathlib PR #39254](https://github.com/leanprover-community/mathlib4/pull/39254),
complex contour integrals by Yury Kudryashov. Our code here will be reviewed upon the
anticipated adoption of those PRs, comparing the results and their assumptions separately.

Limits of finite integrals of exact one-forms depend only on convergence of their
endpoint potential values. The endpoints themselves need not converge in the ambient space.
Integrable half-line pullbacks are also identified with limits of finite path integrals.
Ordinary improper endpoint formulas use Mathlib's fundamental theorem directly.

## Main results

* `tendsto_curveIntegral_of_hasFDerivAt`: Limits of finite integrals of an exact form depend
  only on the limiting endpoint potential values. The endpoints themselves need not converge in
  the ambient space.
* `tendsto_curveIntegral_map_segment`: An integrable half-line pullback is the limit of the
  corresponding finite curve integrals. No primitive for the form is required.
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
