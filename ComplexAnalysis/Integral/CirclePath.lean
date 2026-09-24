/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circles as paths

The usual parametrized complex circle, traversed once counterclockwise, is a `Path`.
Its curve integral agrees with Mathlib's circle integral. The construction and change of
variables allow every real radius, including zero.

## Main results

* `Path.circle_apply`: The circle path uses the angle `2πt`.
* `Path.extend_circle`: On the unit interval, the extended circle path agrees with its smooth
  parametrization.
* `Path.contDiffOn_circle`: The circle path is smooth on its parameter interval.
* `Path.derivWithin_circle`: The derivative of the circle path includes the angle rescaling
  factor `2π`.
* `Complex.curveIntegral_circle`: Curve integration over the circle path agrees with circle
  integration.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set MeasureTheory
open scoped unitInterval

namespace Path

/-- A circle traversed once counterclockwise, starting at `c + R`. -/
@[expose] def circle (c : ℂ) (R : ℝ) : Path (c + R) (c + R) where
  toFun t := circleMap c R (2 * Real.pi * (t : ℝ))
  continuous_toFun := (continuous_circleMap c R).comp (by fun_prop)
  source' := by simp [circleMap]
  target' := by simp [circleMap]

/-- The circle path uses the angle `2πt`. -/
@[simp] theorem circle_apply (c : ℂ) (R : ℝ) (t : I) :
    circle c R t = circleMap c R (2 * Real.pi * (t : ℝ)) := rfl

/-- The circle path covers its entire geometric circle, including for radius zero. -/
theorem range_circle (c : ℂ) (R : ℝ) : Set.range (circle c R) = Metric.sphere c |R| := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact circleMap_mem_sphere' c R _
  · intro hz
    rw [← image_circleMap_Ioc] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    have hp : 0 < 2 * Real.pi := Real.two_pi_pos
    refine ⟨⟨θ / (2 * Real.pi), (div_pos hθ.1 hp).le, (div_le_one hp).mpr hθ.2⟩, ?_⟩
    rw [circle_apply]
    congr 1
    field_simp

/-- A nondegenerate circle path is injective before its final return to the initial point. -/
theorem injOn_circle (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    Set.InjOn (circle c R) {t : I | (t : ℝ) < 1} := by
  intro s hs t ht he
  change (s : ℝ) < 1 at hs
  change (t : ℝ) < 1 at ht
  apply Subtype.ext
  have hp : 0 < 2 * Real.pi := Real.two_pi_pos
  have hst := injOn_circleMap_of_abs_sub_le' (c := c) hR
    (show 2 * Real.pi - 0 ≤ 2 * Real.pi by simp)
    (show 2 * Real.pi * (s : ℝ) ∈ Set.Ico 0 (2 * Real.pi) from
      ⟨mul_nonneg hp.le s.property.1, by nlinarith⟩)
    (show 2 * Real.pi * (t : ℝ) ∈ Set.Ico 0 (2 * Real.pi) from
      ⟨mul_nonneg hp.le t.property.1, by nlinarith⟩) he
  exact mul_left_cancel₀ hp.ne' hst

/-- Mapping a circle path covers exactly the image of its geometric circle. -/
theorem range_map'_circle {Y : Type*} [TopologicalSpace Y] (c : ℂ) (R : ℝ)
    {f : ℂ → Y} (hf : ContinuousOn f (Set.range (circle c R))) :
    Set.range ((circle c R).map' hf) = f '' Metric.sphere c |R| := by
  change Set.range (f ∘ circle c R) = _
  rw [Set.range_comp, range_circle]

/-- Injective maps of the geometric circle preserve simplicity of its parametrization
before the final endpoint. -/
theorem injOn_map'_circle {Y : Type*} [TopologicalSpace Y] (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    {f : ℂ → Y} (hf : ContinuousOn f (Set.range (circle c R)))
    (hi : Set.InjOn f (Metric.sphere c |R|)) :
    Set.InjOn ((circle c R).map' hf) {t : I | (t : ℝ) < 1} := by
  intro s hs t ht he
  exact injOn_circle c hR hs ht (hi (circleMap_mem_sphere' c R _)
    (circleMap_mem_sphere' c R _) he)

/-- On the unit interval, the extended circle path agrees with its smooth parametrization. -/
theorem extend_circle (c : ℂ) (R : ℝ) {t : ℝ} (ht : t ∈ I) :
    (circle c R).extend t = circleMap c R (2 * Real.pi * t) := by
  rw [extend_apply _ ht, circle_apply]

/-- The circle path is smooth on its parameter interval. -/
theorem contDiffOn_circle (c : ℂ) (R : ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (circle c R).extend I := by
  have h : ContDiff ℝ n (fun t : ℝ => circleMap c R (2 * Real.pi * t)) :=
    (contDiff_circleMap c R).comp (contDiff_const.mul contDiff_id)
  exact h.contDiffOn.congr (fun t ht => extend_circle c R ht)

/-- The derivative of the circle path includes the angle rescaling factor `2π`. -/
theorem derivWithin_circle (c : ℂ) (R : ℝ) {t : ℝ} (ht : t ∈ I) :
    derivWithin (circle c R).extend I t =
      (2 * Real.pi) • deriv (circleMap c R) (2 * Real.pi * t) := by
  have h := (hasDerivAt_circleMap c R (2 * Real.pi * t)).scomp t
    ((hasDerivAt_id t).const_mul (2 * Real.pi))
  have h' := h.hasDerivWithinAt.congr_of_mem (fun s hs => extend_circle c R hs) ht
  simpa only [mul_one, deriv_circleMap] using h'.derivWithin (uniqueDiffOn_Icc_zero_one t ht)

end Path

namespace Complex

/-- Curve integration over the circle path agrees with circle integration. -/
theorem curveIntegral_circle {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) (c : ℂ) (R : ℝ) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (Path.circle c R) =
      circleIntegral f c R := by
  rw [curveIntegral_def]
  calc
    _ = ∫ t in (0 : ℝ)..1, (2 * Real.pi) •
        (deriv (circleMap c R) (2 * Real.pi * t) • f (circleMap c R (2 * Real.pi * t))) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      simp only [curveIntegralFun_def, ContinuousLinearMap.toSpanSingleton_apply,
        Path.extend_circle c R ht, Path.derivWithin_circle c R ht, smul_assoc]
    _ = circleIntegral f c R := by
      rw [intervalIntegral.integral_smul,
        intervalIntegral.smul_integral_comp_mul_left
          (f := fun t => deriv (circleMap c R) t • f (circleMap c R t))]
      simp only [mul_zero, mul_one, circleIntegral]

end Complex
