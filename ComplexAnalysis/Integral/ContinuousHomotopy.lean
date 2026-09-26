/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.HasPrimitives.Pullback
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Cauchy's theorem under continuous path deformation

Curve integrals of a holomorphic function agree along differentiable, integrable
paths joined by a continuous homotopy fixing endpoints. No differentiability of
the homotopy or of its intermediate paths is assumed. Local primitives pulled
back to the simply connected parameter square give a continuous potential;
its increments on the boundary compute the two integrals. With moving endpoints,
the two endpoint-track integrals account for the difference. If those integrals
vanish in a family of finite truncations, deformation preserves the limiting integral.

## Main results

* `Complex.curveIntegral_add_curveIntegral_eq_of_continuous_homotopy`: Cauchy's theorem for the
  boundary of a continuous homotopy, with moving endpoints. The four boundary paths must be
  differentiable and integrable, but no regularity of the interior of the homotopy is required
  beyond continuity.
* `Complex.curveIntegral_add_curveIntegral_eq_of_continuous_homotopy_of_contDiffOn`: The
  moving-endpoint Cauchy identity for a continuous homotopy with `C¹` boundary paths.
* `Complex.curveIntegral_eq_of_continuous_homotopy`: Holomorphic curve integrals agree under a
  continuous homotopy fixing endpoints. Only the two boundary paths must be differentiable and
  curve integrable.
* `Complex.curveIntegral_eq_of_continuous_homotopy_of_contDiffOn`: A continuous homotopy in a
  holomorphy domain preserves integrals along `C¹` boundary paths.
* `Complex.tendsto_curveIntegral_of_continuous_homotopy`: Deformation preserves a limit of
  finite curve integrals when the integrals along both endpoint tracks vanish. This applies to
  improper contours via their finite truncations.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace Complex

/-- Cauchy's theorem for the boundary of a continuous homotopy, with moving endpoints.
The four boundary paths must be differentiable and integrable, but no regularity of
the interior of the homotopy is required beyond continuity. -/
theorem curveIntegral_add_curveIntegral_eq_of_continuous_homotopy
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} {a b c d : ℂ} {γ : Path a b} {δ : Path c d}
    (H : (γ : C(I, ℂ)).Homotopy δ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : range H ⊆ U)
    (hγ : DifferentiableOn ℝ γ.extend I) (hδ : DifferentiableOn ℝ δ.extend I)
    (h₀ : DifferentiableOn ℝ (H.evalAt 0).extend I)
    (h₁ : DifferentiableOn ℝ (H.evalAt 1).extend I)
    (hiγ : CurveIntegrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ)
    (hiδ : CurveIntegrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ)
    (hi₀ : CurveIntegrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 0))
    (hi₁ : CurveIntegrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 1)) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ +
        curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 1) =
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ +
        curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 0) := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨Q, hQ, _, hlocal⟩ := hf.exists_continuous_primitive_pullback hU H.continuous
    hHU ((0 : I), (0 : I)) 0
  have heγ := curveIntegral_eq_sub_of_locally_primitive H.continuous hQ hlocal
    (r := fun t : I ↦ ((0 : I), t)) (by fun_prop) (fun t ↦ H.apply_zero t) hγ hiγ
  have heδ := curveIntegral_eq_sub_of_locally_primitive H.continuous hQ hlocal
    (r := fun t : I ↦ ((1 : I), t)) (by fun_prop) (fun t ↦ H.apply_one t) hδ hiδ
  have he₀ := curveIntegral_eq_sub_of_locally_primitive H.continuous hQ hlocal
    (r := fun t : I ↦ (t, (0 : I))) (by fun_prop) (fun _ ↦ rfl) h₀ hi₀
  have he₁ := curveIntegral_eq_sub_of_locally_primitive H.continuous hQ hlocal
    (r := fun t : I ↦ (t, (1 : I))) (by fun_prop) (fun _ ↦ rfl) h₁ hi₁
  rw [heγ, heδ, he₀, he₁]
  abel

/-- The moving-endpoint Cauchy identity for a continuous homotopy with `C¹` boundary paths. -/
theorem curveIntegral_add_curveIntegral_eq_of_continuous_homotopy_of_contDiffOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} {a b c d : ℂ} {γ : Path a b} {δ : Path c d}
    (H : (γ : C(I, ℂ)).Homotopy δ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : range H ⊆ U)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hδ : ContDiffOn ℝ 1 δ.extend I)
    (h₀ : ContDiffOn ℝ 1 (H.evalAt 0).extend I)
    (h₁ : ContDiffOn ℝ 1 (H.evalAt 1).extend I) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ +
        curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 1) =
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ +
        curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 0) :=
  curveIntegral_add_curveIntegral_eq_of_continuous_homotopy H hU hf hHU
    (hγ.differentiableOn one_ne_zero) (hδ.differentiableOn one_ne_zero)
    (h₀.differentiableOn one_ne_zero) (h₁.differentiableOn one_ne_zero)
    (curveIntegrable_of_continuousOn hf.continuousOn hγ
      (fun t ↦ hHU ⟨(0, t), H.apply_zero t⟩))
    (curveIntegrable_of_continuousOn hf.continuousOn hδ
      (fun t ↦ hHU ⟨(1, t), H.apply_one t⟩))
    (curveIntegrable_of_continuousOn hf.continuousOn h₀ (fun t ↦ hHU ⟨(t, 0), rfl⟩))
    (curveIntegrable_of_continuousOn hf.continuousOn h₁ (fun t ↦ hHU ⟨(t, 1), rfl⟩))

/-- Holomorphic curve integrals agree under a continuous homotopy fixing endpoints.
Only the two boundary paths must be differentiable and curve integrable. -/
theorem curveIntegral_eq_of_continuous_homotopy
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} {a b : ℂ} {γ δ : Path a b} (H : γ.Homotopy δ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : range H ⊆ U)
    (hγ : DifferentiableOn ℝ γ.extend I) (hδ : DifferentiableOn ℝ δ.extend I)
    (hγint : CurveIntegrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ)
    (hδint : CurveIntegrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ =
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨Q, hQ, _, hlocal⟩ := hf.exists_continuous_primitive_pullback hU H.continuous
    hHU ((0 : I), (0 : I)) 0
  have hedge (t : I) (ht : ∀ s, H (s, t) = H (0, t)) : ∀ s, Q (s, t) = Q (0, t) := by
    suffices hc : IsLocallyConstant (fun s : I ↦ Q (s, t)) from
      fun s ↦ hc.apply_eq_of_preconnectedSpace s 0
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro s
    obtain ⟨P, _, he⟩ := hlocal (s, t)
    have hc : ContinuousAt (fun r : I ↦ (r, t)) s := by fun_prop
    filter_upwards [hc.eventually he] with r hr
    simpa only [ht r, ht s, sub_self, add_zero] using hr
  let η (s : I) : Path (s, (0 : I)) (s, (1 : I)) := (Path.refl s).prod Path.id
  have hmap (s : I) : (η s).map H.continuous =
      (H.eval s).cast (H.source s) (H.target s) := by
    ext t
    rfl
  have hrow (s : I) (hs : DifferentiableOn ℝ (H.eval s).extend I)
      (hint : CurveIntegrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.eval s)) :
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.eval s) =
        Q (s, 1) - Q (s, 0) := by
    have h := curveIntegral_map_eq_sub_of_locally_primitive H.continuous hQ hlocal (η s)
      (by simpa only [hmap, Path.extend_cast] using hs)
      (by simpa only [hmap, curveIntegrable_cast_iff] using hint)
    simpa only [hmap, curveIntegral_cast] using h
  have hγeq := hrow 0 (by simpa using hγ) (by simpa using hγint)
  have hδeq := hrow 1 (by simpa using hδ) (by simpa using hδint)
  simp only [Path.Homotopy.eval_zero, Path.Homotopy.eval_one] at hγeq hδeq
  rw [hedge 0 (by intro s; simp) 1, hedge 1 (by intro s; simp) 1] at hδeq
  exact hγeq.trans hδeq.symm

/-- A continuous homotopy in a holomorphy domain preserves integrals along `C¹` boundary paths. -/
theorem curveIntegral_eq_of_continuous_homotopy_of_contDiffOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} {a b : ℂ} {γ δ : Path a b} (H : γ.Homotopy δ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : range H ⊆ U)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hδ : ContDiffOn ℝ 1 δ.extend I) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ =
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ :=
  curveIntegral_eq_of_continuous_homotopy H hU hf hHU
    (hγ.differentiableOn one_ne_zero) (hδ.differentiableOn one_ne_zero)
    (curveIntegrable_of_continuousOn hf.continuousOn hγ
      (fun t ↦ hHU ⟨(0, t), by simp⟩))
    (curveIntegrable_of_continuousOn hf.continuousOn hδ
      (fun t ↦ hHU ⟨(1, t), by simp⟩))

/-- Deformation preserves a limit of finite curve integrals when the integrals along
both endpoint tracks vanish. This applies to improper contours via their finite truncations. -/
theorem tendsto_curveIntegral_of_continuous_homotopy
    {F α : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {ℱ : Filter α} {U : Set ℂ} {f : ℂ → F} {a b c d : α → ℂ}
    {γ : ∀ i, Path (a i) (b i)} {δ : ∀ i, Path (c i) (d i)}
    (H : ∀ i, (γ i : C(I, ℂ)).Homotopy (δ i))
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : ∀ i, range (H i) ⊆ U)
    (hγ : ∀ i, ContDiffOn ℝ 1 (γ i).extend I) (hδ : ∀ i, ContDiffOn ℝ 1 (δ i).extend I)
    (h₀ : ∀ i, ContDiffOn ℝ 1 ((H i).evalAt 0).extend I)
    (h₁ : ∀ i, ContDiffOn ℝ 1 ((H i).evalAt 1).extend I)
    {v : F}
    (hlim : Tendsto (fun i ↦ curveIntegral
      (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (γ i)) ℱ (𝓝 v))
    (hstart : Tendsto (fun i ↦ curveIntegral
      (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) ((H i).evalAt 0)) ℱ (𝓝 0))
    (hend : Tendsto (fun i ↦ curveIntegral
      (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) ((H i).evalAt 1)) ℱ (𝓝 0)) :
    Tendsto (fun i ↦ curveIntegral
      (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (δ i)) ℱ (𝓝 v) := by
  have he i := curveIntegral_add_curveIntegral_eq_of_continuous_homotopy_of_contDiffOn
    (H i) hU hf (hHU i) (hγ i) (hδ i) (h₀ i) (h₁ i)
  simpa only [add_zero, sub_zero] using
    ((hlim.add hend).sub hstart).congr (fun i ↦ (eq_sub_of_add_eq (he i).symm).symm)

end Complex
