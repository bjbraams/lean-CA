/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Cauchy's formula along closed curves in simply connected domains

For a closed `C¹` curve in a simply connected open domain, the integral of the Cauchy kernel times a
holomorphic function is the kernel integral times the value at the pole. The function may
take values in any complex Banach space. The kernel integral is retained explicitly, so this
statement does not assume a Jordan interior, an orientation, or a winding-number theorem.
The usual normalized formula follows when the kernel integral is `2 * π * I`.

## Main results

* `Complex.curveIntegral_smul_const`: A constant Banach-valued factor can be taken outside a
  scalar curve integral.
* `Complex.curveIntegral_sub_inv_smul_of_convex`: Cauchy's formula for a closed `C¹` curve in a
  convex open domain, with the scalar kernel integral explicit. No simplicity assumption on the
  curve is needed.
* `Complex.curveIntegral_sub_inv_smul_of_isSimplyConnected`: Cauchy's formula for a closed `C¹`
  curve in a simply connected open domain, with the scalar kernel integral explicit. No
  simplicity assumption on the curve is needed.
* `Complex.two_pi_I_inv_smul_curveIntegral_sub_inv_smul_of_convex`: The normalized Cauchy
  formula follows once the scalar kernel integral has value `2πi`. Determining this value from
  the geometry and orientation of a contour is a separate theorem.
* `Complex.two_pi_I_inv_smul_curveIntegral_sub_inv_smul_of_isSimplyConnected`: The normalized
  Cauchy formula follows once the scalar kernel integral has value `2πi`. Determining this value
  from the geometry and orientation of a contour is a separate theorem.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public section

open Set MeasureTheory
open scoped unitInterval Topology

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {a b : ℂ} {γ : Path a b}

/-- A constant Banach-valued factor can be taken outside a scalar curve integral. -/
theorem curveIntegral_smul_const {g : ℂ → ℂ} (v : F)
    (hint : CurveIntegrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (g z)) γ) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (g z • v)) γ =
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (g z)) γ • v := by
  simpa only [ContinuousLinearMap.toSpanSingleton_comp_toSpanSingleton,
    ContinuousLinearMap.toSpanSingleton_apply] using
    (ContinuousLinearMap.toSpanSingleton ℂ v).curveIntegral_comp_comm hint

/-- Cauchy's formula along a closed `C¹` curve whenever the divided slope has a primitive.
The scalar kernel integral remains explicit. -/
theorem curveIntegral_sub_inv_smul_of_isExactOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → F} (hf : ContinuousOn f U) {w : ℂ} (hds : IsExactOn (dslope f w) U)
    {γ : Path a a} (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ t, γ t ∈ U)
    (hγw : ∀ t, γ t ≠ w) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹ • f z)) γ =
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ • f w := by
  have hinv : ContinuousOn (fun z : ℂ ↦ (z - w)⁻¹) ({w}ᶜ : Set ℂ) :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ (fun z hz ↦ sub_ne_zero.mpr hz)
  have hpath : ∀ t, γ t ∈ U ∩ {w}ᶜ := fun t ↦ ⟨hγU t, hγw t⟩
  have hA := curveIntegrable_of_continuousOn
    ((hinv.mono inter_subset_right).smul (hf.mono inter_subset_left)) hγ hpath
  have hB := curveIntegrable_of_continuousOn (hinv.smul (continuousOn_const (c := f w)))
    hγ hγw
  change CurveIntegrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ
    ((z - w)⁻¹ • f z)) γ at hA
  change CurveIntegrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ
    ((z - w)⁻¹ • f w)) γ at hB
  have hscalar := curveIntegrable_of_continuousOn hinv hγ hγw
  have hzero := hds.curveIntegral_eq_zero (hγ.differentiableOn one_ne_zero) hγU
    (curveIntegrable_of_continuousOn (hds.differentiableOn hU).continuousOn hγ hγU)
  have heq : curveIntegral
      (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹ • f z) -
        ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹ • f w)) γ = 0 := by
    rw [← hzero]
    apply curveIntegral_congr
    intro t
    ext
    simp [dslope_of_ne _ (hγw t), slope_def_module, smul_sub]
  rw [curveIntegral_fun_sub hA hB] at heq
  exact (sub_eq_zero.mp heq).trans (curveIntegral_smul_const (f w) hscalar)

/-- Cauchy's formula for a closed `C¹` curve in a convex open domain, with the scalar kernel
integral explicit. No simplicity assumption on the curve is needed. -/
theorem curveIntegral_sub_inv_smul_of_convex {U : Set ℂ} (hU : IsOpen U)
    (hUc : Convex ℝ U) {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    {w : ℂ} (hw : w ∈ U) {γ : Path a a}
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ t, γ t ∈ U)
    (hγw : ∀ t, γ t ≠ w) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹ • f z)) γ =
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ • f w := by
  have hds := (differentiableOn_dslope (hU.mem_nhds hw)).mpr hf
  obtain ⟨P, hP⟩ := hUc.exists_forall_hasDerivWithinAt hds
  exact curveIntegral_sub_inv_smul_of_isExactOn hU hf.continuousOn
    ⟨P, fun z hz ↦ (hP z hz).hasDerivAt (hU.mem_nhds hz)⟩ hγ hγU hγw

/-- Cauchy's formula for a closed `C¹` curve in a simply connected open domain, with the scalar
kernel
integral explicit. No simplicity assumption on the curve is needed. -/
theorem curveIntegral_sub_inv_smul_of_isSimplyConnected {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    {w : ℂ} (hw : w ∈ U) {γ : Path a a}
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ t, γ t ∈ U)
    (hγw : ∀ t, γ t ≠ w) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹ • f z)) γ =
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ • f w := by
  have hds := (differentiableOn_dslope (hU.mem_nhds hw)).mpr hf
  exact curveIntegral_sub_inv_smul_of_isExactOn hU hf.continuousOn
    (hds.isExactOn_of_isSimplyConnected hU hUc) hγ hγU hγw

/-- The normalized Cauchy formula follows once the scalar kernel integral has value `2πi`.
Determining this value from the geometry and orientation of a contour is a separate theorem. -/
theorem two_pi_I_inv_smul_curveIntegral_sub_inv_smul_of_convex
    {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) {w : ℂ} (hw : w ∈ U)
    {γ : Path a a} (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ t, γ t ∈ U)
    (hγw : ∀ t, γ t ≠ w)
    (hindex : curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ =
      2 * (Real.pi : ℂ) * Complex.I) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹ • f z)) γ =
        f w := by
  rw [curveIntegral_sub_inv_smul_of_convex hU hUc hf hw hγ hγU hγw, hindex,
    inv_smul_smul₀ two_pi_I_ne_zero]

/-- The normalized Cauchy formula follows once the scalar kernel integral has value `2πi`.
Determining this value from the geometry and orientation of a contour is a separate theorem. -/
theorem two_pi_I_inv_smul_curveIntegral_sub_inv_smul_of_isSimplyConnected
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsSimplyConnected U)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) {w : ℂ} (hw : w ∈ U)
    {γ : Path a a} (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ t, γ t ∈ U)
    (hγw : ∀ t, γ t ≠ w)
    (hindex : curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ =
      2 * (Real.pi : ℂ) * Complex.I) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹ • f z)) γ =
        f w := by
  rw [curveIntegral_sub_inv_smul_of_isSimplyConnected hU hUc hf hw hγ hγU hγw, hindex,
    inv_smul_smul₀ two_pi_I_ne_zero]

end Complex
