/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CauchyPompeiu
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth cutoffs and the Cauchy–Pompeiu representation of holomorphic functions

A holomorphic function `f` on an open set `U` is represented on a compact subset `K` by a
Cauchy-type integral `f z = ∫ w in Ω, g w * (w - z)⁻¹` whose density `g` is continuous and
supported in a compact set `Ω ⊆ U \ K`: with a smooth cutoff `φ` equal to `1` near `K` and
compactly supported in `U`, the Cauchy–Pompeiu identity applied to the translates of `φ f` gives
`g = -π⁻¹ f ∂φ/∂z̄`. This is the representation used in the proof of Runge's theorem that avoids
contour constructions (Hörmander 1.4.4; Rudin, *Real and Complex Analysis*, 13.6 uses a cycle
instead).

## Main results

* `Complex.exists_smooth_cutoff`: a `C¹` cutoff equal to `1` near a compact set and compactly
  supported in a given open neighborhood.
* `Complex.exists_cauchyPompeiu_representation`: the representation of a holomorphic function
  on a compact set by a Cauchy-type integral with continuous density supported off the set.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set MeasureTheory Metric Filter Function
open scoped Topology Real

namespace Complex

/-- A `C¹` cutoff function: equal to `1` on a neighborhood of a compact set, with compact
support inside a given open neighborhood, and values in `[0, 1]`. -/
theorem exists_smooth_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
      (∀ x, φ x ∈ Icc 0 1) ∧ ∃ W, IsOpen W ∧ K ⊆ W ∧ EqOn φ 1 W := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W, hWo, hKW, hWV, _⟩ := exists_open_between_and_isCompact_closure hK hVo hKV
  obtain ⟨f, h0, h1, hI⟩ := exists_contMDiffMap_zero_one_of_isClosed (modelWithCornersSelf ℝ ℂ)
    (M := ℂ) (n := ⊤) hVo.isClosed_compl isClosed_closure (disjoint_compl_left_iff.mpr hWV)
  have hsupp : support f ⊆ V := by
    intro x hx
    by_contra hxV
    exact hx (h0 hxV)
  refine ⟨f, f.contMDiff.contDiff.of_le (by exact_mod_cast le_top), ?_, ?_, hI, W, hWo, hKW,
    fun x hx => h1 (subset_closure hx)⟩
  · exact HasCompactSupport.of_support_subset_isCompact hVc (hsupp.trans subset_closure)
  · exact (closure_mono hsupp).trans hVU

/-- The antiholomorphic part is compatible with complex scalar multiples of a real-linear map
into `ℂ`. -/
theorem dbarAlong_smul (a : ℂ) (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    dbarAlong (a • L) v = a * dbarAlong L v := by
  simp only [dbarAlong, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The antiholomorphic part of the real derivative of a product `ψ * f`, with `f` complex
differentiable, is `f` times the antiholomorphic part of the derivative of `ψ`. -/
theorem dbarAlong_fderiv_mul {ψ f : ℂ → ℂ} {u : ℂ} (hψ : DifferentiableAt ℝ ψ u)
    (hf : DifferentiableAt ℂ f u) :
    dbarAlong (fderiv ℝ (fun w => ψ w * f w) u) 1 = f u * dbarAlong (fderiv ℝ ψ u) 1 := by
  change dbarAlong (fderiv ℝ (ψ * f) u) 1 = _
  rw [fderiv_mul hψ (hf.restrictScalars ℝ), dbarAlong_add, dbarAlong_smul, dbarAlong_smul,
    hf.fderiv_restrictScalars ℝ, dbarAlong_restrictScalars, mul_zero, zero_add]

/-- **Cauchy–Pompeiu representation on a compact set.** A holomorphic function on an open set
`U` is represented on a compact subset `K` by a Cauchy-type integral with a continuous density
supported in a compact subset of `U \ K`. -/
theorem exists_cauchyPompeiu_representation {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ (Ω : Set ℂ) (g : ℂ → ℂ), IsCompact Ω ∧ Ω ⊆ U \ K ∧ Continuous g ∧
      (∀ w, w ∉ Ω → g w = 0) ∧ ∀ z ∈ K, f z = ∫ w in Ω, g w * (w - z)⁻¹ := by
  obtain ⟨φ, hφ, hφsupp, hφU, _, W, hWo, hKW, hφW⟩ := exists_smooth_cutoff hK hU hKU
  set ψ : ℂ → ℂ := fun w => (φ w : ℂ) with hψ_def
  have hψ : ContDiff ℝ 1 ψ := ofRealCLM.contDiff.comp hφ
  have hψsupp' : support ψ ⊆ support φ := fun w hw h => hw (by simp [ψ, h])
  have hψt : tsupport ψ ⊆ tsupport φ := closure_mono hψsupp'
  have hψsupp : HasCompactSupport ψ := hφsupp.of_isClosed_subset isClosed_closure hψt
  have hψU : tsupport ψ ⊆ U := hψt.trans hφU
  have hψW : EqOn ψ 1 W := fun w hw => by simp [ψ, hφW hw]
  have hfderiv_zero : ∀ w, w ∉ tsupport ψ \ W → fderiv ℝ ψ w = 0 := by
    intro w hw
    by_cases hwW : w ∈ W
    · have : ψ =ᶠ[𝓝 w] fun _ => 1 := by
        filter_upwards [hWo.mem_nhds hwW] with v hv
        exact hψW hv
      rw [this.fderiv_eq, fderiv_const_apply]
    · have hwt : w ∉ tsupport ψ := fun h => hw ⟨h, hwW⟩
      exact image_eq_zero_of_notMem_tsupport fun h => hwt (tsupport_fderiv_subset ℝ h)
  set Ω : Set ℂ := tsupport ψ \ W with hΩ_def
  have hΩc : IsCompact Ω := hψsupp.diff hWo
  have hΩUK : Ω ⊆ U \ K := fun w hw => ⟨hψU hw.1, fun hK => hw.2 (hKW hK)⟩
  set g₀ : ℂ → ℂ := fun w => f w * dbarAlong (fderiv ℝ ψ w) 1 with hg₀_def
  set g : ℂ → ℂ := fun w => -(π : ℂ)⁻¹ * g₀ w with hg_def
  have hg₀zero : ∀ w, w ∉ Ω → g₀ w = 0 := fun w hw => by
    simp [g₀, hfderiv_zero w hw, dbarAlong_zero]
  have hgzero : ∀ w, w ∉ Ω → g w = 0 := fun w hw => by simp [g, hg₀zero w hw]
  -- continuity of the density
  have hdbar : Continuous fun w => dbarAlong (fderiv ℝ ψ w) 1 := by
    have hc := hψ.continuous_fderiv one_ne_zero
    simp only [dbarAlong]
    fun_prop
  have hg₀cont : Continuous g₀ := by
    rw [continuous_iff_continuousAt]
    intro w
    by_cases hwU : w ∈ U
    · exact (hf.continuousOn.continuousAt (hU.mem_nhds hwU)).mul hdbar.continuousAt
    · have hwt : w ∉ tsupport ψ := fun h => hwU (hψU h)
      have : g₀ =ᶠ[𝓝 w] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hwt] with v hv
        exact hg₀zero v fun h => hv h.1
      exact continuousAt_const.congr_of_eventuallyEq this
  have hgcont : Continuous g := continuous_const.mul hg₀cont
  refine ⟨Ω, g, hΩc, hΩUK, hgcont, hgzero, fun z hz => ?_⟩
  -- the translated product `Φ w = ψ (w + z) * f (w + z)`
  set Φ : ℂ → ℂ := fun w => ψ (w + z) * f (w + z) with hΦ_def
  have hprod : ∀ u, dbarAlong (fderiv ℝ (fun w => ψ w * f w) u) 1 = g₀ u := by
    intro u
    by_cases huU : u ∈ U
    · exact dbarAlong_fderiv_mul (hψ.differentiable one_ne_zero u)
        (hf.differentiableAt (hU.mem_nhds huU))
    · have hut : u ∉ tsupport ψ := fun h => huU (hψU h)
      have hev : (fun w => ψ w * f w) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hut] with v hv
        simp [image_eq_zero_of_notMem_tsupport hv]
      rw [hev.fderiv_eq, fderiv_const_apply, dbarAlong_zero]
      simp [g₀, hfderiv_zero u fun h => hut h.1, dbarAlong_zero]
  have hΦdiff : ContDiff ℝ 1 Φ := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hwU : w + z ∈ U
    · have hf' : ContDiffAt ℝ 1 f (w + z) :=
        ((DifferentiableOn.analyticOnNhd hf hU) (w + z) hwU).contDiffAt.restrict_scalars ℝ
      exact (hψ.contDiffAt.mul hf').comp w (contDiffAt_id.add contDiffAt_const)
    · have hwt : w + z ∉ tsupport ψ := fun h => hwU (hψU h)
      have hev : Φ =ᶠ[𝓝 w] fun _ => 0 := by
        have hmem : (fun v => v + z) ⁻¹' (tsupport ψ)ᶜ ∈ 𝓝 w :=
          (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
            ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hwt)
        filter_upwards [hmem] with v hv
        simp [Φ, image_eq_zero_of_notMem_tsupport hv]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hΦsupp : HasCompactSupport Φ :=
    (hψsupp.mul_right).comp_homeomorph (Homeomorph.addRight z)
  have hpompeiu := integral_inv_smul_dbarAlong_fderiv hΦdiff hΦsupp
  have hΦ0 : Φ 0 = f z := by simp [Φ, hψW (hKW hz)]
  have hΦderiv : ∀ w, dbarAlong (fderiv ℝ Φ w) 1 = g₀ (w + z) := by
    intro w
    have : fderiv ℝ Φ w = fderiv ℝ (fun w => ψ w * f w) (w + z) := by
      change fderiv ℝ (fun x => (fun w => ψ w * f w) (x + z)) w = _
      exact fderiv_comp_add_right (𝕜 := ℝ) (f := fun w => ψ w * f w) (x := w) z
    rw [this, hprod]
  simp only [hΦderiv, hΦ0, smul_eq_mul] at hpompeiu
  have htrans : ∫ w, w⁻¹ * g₀ (w + z) = ∫ w, (w - z)⁻¹ * g₀ w := by
    have := integral_add_right_eq_self (μ := volume) (fun w => (w - z)⁻¹ * g₀ w) z
    simpa only [add_sub_cancel_right] using this
  rw [htrans] at hpompeiu
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => by simp [hgzero w hw]]
  simp only [g]
  rw [show (fun w => -(π : ℂ)⁻¹ * g₀ w * (w - z)⁻¹) =
      fun w => -(π : ℂ)⁻¹ * ((w - z)⁻¹ * g₀ w) from funext fun w => by ring,
    integral_const_mul, hpompeiu]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [neg_mul_neg, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

end Complex

end
