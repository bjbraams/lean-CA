/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Cycle
public import ComplexAnalysis.HolomorphicIntegral
public import Mathlib.Analysis.Complex.Liouville

/-!
# The homology form of Cauchy's theorem

A cycle `Γ` in an open set `U` is *homologous to zero in `U`* if its index vanishes at every
point outside `U`. For such cycles Cauchy's integral formula and Cauchy's theorem hold for every
Banach-valued function holomorphic on `U`, with the index as weight in the formula. The proof is
Dixon's: the integral over the cycle of the divided slope `dslope f w z` is holomorphic in `z`
on `U`, agrees off the cycle with the Cauchy integral wherever the index vanishes, and the two
pieces glue to a bounded entire function vanishing at infinity.

## Main results

* `Complex.Cycle.integral_dslope_eq_zero`: the integral of the divided slope over a cycle
  homologous to zero vanishes.
* `Complex.Cycle.integral_sub_inv_smul_eq_index_smul`: Cauchy's integral formula for cycles.
* `Complex.Cycle.integral_eq_zero`: Cauchy's theorem for cycles.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorem IV.5.4.
* B. Simon, *Basic Complex Analysis*, Theorem 4.2.1.
-/

public noncomputable section

open Set MeasureTheory Metric Filter ContinuousLinearMap
open scoped unitInterval Topology

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The curve integral of a jointly continuous kernel that is holomorphic in a complex parameter
is holomorphic in that parameter. -/
theorem differentiableOn_curveIntegral_kernel {U : Set ℂ} (hU : IsOpen U) {a : ℂ}
    {γ : Path a a} (hγ : ContDiffOn ℝ 1 γ.extend I) {V : Set ℂ} (hγV : ∀ t, γ t ∈ V)
    {K : ℂ → ℂ → F} (hK : ContinuousOn (fun p : ℂ × ℂ ↦ K p.1 p.2) (U ×ˢ V))
    (hd : ∀ w ∈ V, DifferentiableOn ℂ (fun z ↦ K z w) U) :
    DifferentiableOn ℂ (fun z ↦ curveIntegral (fun w ↦ toSpanSingleton ℂ (K z w)) γ) U := by
  have hV : ∀ t : ℝ, γ.extend t ∈ V := fun t ↦ by
    obtain ⟨s, hs⟩ : γ.extend t ∈ Set.range γ := γ.extend_range ▸ mem_range_self t
    rw [← hs]
    exact hγV s
  simp only [curveIntegral_def, curveIntegralFun_def, toSpanSingleton_apply]
  refine differentiableOn_intervalIntegral_of_continuousOn hU zero_le_one ?_ ?_
  · have hder : ContinuousOn (fun p : ℂ × ℝ ↦ derivWithin γ.extend I p.2) (U ×ˢ Icc 0 1) :=
      (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).comp
        continuous_snd.continuousOn fun p hp ↦ hp.2
    refine hder.smul ?_
    refine hK.comp (f := fun p : ℂ × ℝ ↦ (p.1, γ.extend p.2)) ?_ ?_
    · exact continuous_fst.continuousOn.prodMk (γ.continuous_extend.comp_continuousOn
        continuous_snd.continuousOn)
    · rintro ⟨z, t⟩ ⟨hz, _⟩
      exact ⟨hz, hV t⟩
  · intro t _
    exact (hd _ (hV t)).const_smul _

namespace Cycle

variable (Γ : Cycle)

/-- The integral of a jointly continuous kernel holomorphic in a parameter over a cycle is
holomorphic in that parameter. -/
theorem differentiableOn_integral_kernel {U : Set ℂ} (hU : IsOpen U) (hΓ : Γ.IsC1)
    {V : Set ℂ} (hΓV : Γ.range ⊆ V)
    {K : ℂ → ℂ → F} (hK : ContinuousOn (fun p : ℂ × ℂ ↦ K p.1 p.2) (U ×ˢ V))
    (hd : ∀ w ∈ V, DifferentiableOn ℂ (fun z ↦ K z w) U) :
    DifferentiableOn ℂ (fun z ↦ Γ.integral (fun w ↦ toSpanSingleton ℂ (K z w))) U := by
  unfold Cycle.integral
  refine (DifferentiableOn.sum (u := Finset.univ) fun i _ ↦
    differentiableOn_curveIntegral_kernel hU (hΓ i) (fun t ↦ hΓV (Γ.loop_mem_range i t))
      hK hd).congr fun z _ ↦ ?_
  simp [Finset.sum_apply]

/-- Off the cycle, the integral of the divided slope is the Cauchy integral minus the index
term. Only continuity of the function on a set containing the cycle is used. -/
theorem integral_dslope_eq_sub (hΓ : Γ.IsC1) {U : Set ℂ} (hΓU : Γ.range ⊆ U)
    {f : ℂ → F} (hf : ContinuousOn f U) {z : ℂ} (hz : z ∉ Γ.range) :
    Γ.integral (fun w ↦ toSpanSingleton ℂ (dslope f w z)) =
      Γ.integral (fun w ↦ toSpanSingleton ℂ ((w - z)⁻¹ • f w)) -
        (2 * (Real.pi : ℂ) * Complex.I * Γ.index z) • f z := by
  have hne : ∀ w ∈ Γ.range, w - z ≠ 0 := fun w hw h ↦ hz (sub_eq_zero.mp h ▸ hw)
  have hker : ContinuousOn (fun w ↦ (w - z)⁻¹) Γ.range :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  have hint₁ : Γ.Integrable (fun w ↦ toSpanSingleton ℂ ((w - z)⁻¹ • f w)) :=
    Γ.integrable_toSpanSingleton_of_continuousOn hΓ (hker.smul (hf.mono hΓU)) subset_rfl
  have hint₂ : Γ.Integrable (fun w ↦ toSpanSingleton ℂ ((w - z)⁻¹)) :=
    Γ.integrable_toSpanSingleton_of_continuousOn hΓ hker subset_rfl
  have hint₃ : Γ.Integrable (fun w ↦ toSpanSingleton ℂ ((w - z)⁻¹ • f z)) :=
    Γ.integrable_toSpanSingleton_of_continuousOn hΓ (hker.smul continuousOn_const) subset_rfl
  have hcongr : EqOn (fun w ↦ toSpanSingleton ℂ (dslope f w z))
      ((fun w ↦ toSpanSingleton ℂ ((w - z)⁻¹ • f w)) -
        fun w ↦ toSpanSingleton ℂ ((w - z)⁻¹ • f z)) Γ.range := by
    intro w hw
    have hwz : z ≠ w := fun h ↦ hz (h ▸ hw)
    have key : dslope f w z = (w - z)⁻¹ • f w - (w - z)⁻¹ • f z := by
      rw [dslope_of_ne _ hwz, slope_def_module, ← neg_sub w z, inv_neg, neg_smul, smul_sub,
        neg_sub]
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp [key, smul_sub]
  rw [Γ.integral_congr hcongr, Γ.integral_sub hint₁ hint₃, Γ.integral_smul_const (f z) hint₂,
    Γ.integral_sub_inv_eq_two_pi_I_mul_index]

/-- **Dixon's lemma.** For a `C¹` cycle in an open set `U` whose index vanishes outside `U`,
and a Banach-valued function holomorphic on `U`, the integral over the cycle of the divided
slope at any point of `U` vanishes. -/
theorem integral_dslope_eq_zero {U : Set ℂ} (hU : IsOpen U) (hΓ : Γ.IsC1)
    (hΓU : Γ.range ⊆ U) (hind : ∀ w, w ∉ U → Γ.index w = 0)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) :
    Γ.integral (fun w ↦ toSpanSingleton ℂ (dslope f w z)) = 0 := by
  classical
  set h : ℂ → F := fun z ↦ Γ.integral (fun w ↦ toSpanSingleton ℂ (dslope f w z)) with hh_def
  set h₁ : ℂ → F := fun z ↦ Γ.integral (fun w ↦ toSpanSingleton ℂ ((w - z)⁻¹ • f w))
    with hh₁_def
  have hh : DifferentiableOn ℂ h U := by
    refine Γ.differentiableOn_integral_kernel hU hΓ (V := U) hΓU
      (K := fun z w ↦ dslope f w z) ?_ ?_
    · exact (continuousOn_dslope_prod_of_differentiableOn hU hf).comp
        (f := fun p : ℂ × ℂ ↦ (p.2, p.1)) (by fun_prop) fun p hp ↦ ⟨hp.2, hp.1⟩
    · intro w hw
      exact (differentiableOn_dslope (hU.mem_nhds hw)).mpr hf
  have hh₁ : DifferentiableOn ℂ h₁ Γ.rangeᶜ := by
    refine Γ.differentiableOn_integral_kernel Γ.isOpen_compl_range hΓ (V := Γ.range) subset_rfl
      (K := fun z w ↦ (w - z)⁻¹ • f w) ?_ ?_
    · refine ContinuousOn.smul ?_ (hf.continuousOn.comp continuous_snd.continuousOn
        fun p hp ↦ hΓU hp.2)
      refine ContinuousOn.inv₀ (continuous_snd.continuousOn.sub continuous_fst.continuousOn) ?_
      rintro ⟨z, w⟩ ⟨hz, hw⟩
      exact sub_ne_zero.mpr fun h ↦ (hz : z ∉ Γ.range) (h ▸ hw)
    · intro w hw
      exact (((differentiableOn_const w).sub differentiableOn_id).inv
        fun z hz ↦ sub_ne_zero.mpr fun h ↦ (hz : z ∉ Γ.range)
          ((show w = z from h) ▸ hw)).smul_const (f w)
  have hagree : ∀ z, z ∉ Γ.range → Γ.index z = 0 → z ∈ U → h z = h₁ z := by
    intro z hzΓ hzi _
    simp only [hh_def, hh₁_def]
    rw [Γ.integral_dslope_eq_sub hΓ hΓU hf.continuousOn hzΓ, hzi, mul_zero, zero_smul,
      sub_zero]
  have hV : IsOpen {w | w ∉ Γ.range ∧ Γ.index w = 0} := Γ.isOpen_setOf_index_eq hΓ 0
  let H : ℂ → F := fun z ↦ if z ∈ U then h z else h₁ z
  have hHU : ∀ z ∈ U, H z = h z := fun z hz ↦ by simp [H, hz]
  have hHV : ∀ z, z ∉ Γ.range → Γ.index z = 0 → H z = h₁ z := by
    intro z hzΓ hzi
    by_cases hzU : z ∈ U
    · simp [H, hzU, hagree z hzΓ hzi hzU]
    · simp [H, hzU]
  have hHdiff : Differentiable ℂ H := by
    intro z₀
    by_cases hz₀ : z₀ ∈ U
    · have heq : H =ᶠ[𝓝 z₀] h := by
        filter_upwards [hU.mem_nhds hz₀] with z hz
        exact hHU z hz
      exact heq.differentiableAt_iff.mpr (hh.differentiableAt (hU.mem_nhds hz₀))
    · have hz₀Γ : z₀ ∉ Γ.range := fun hm ↦ hz₀ (hΓU hm)
      have heq : H =ᶠ[𝓝 z₀] h₁ := by
        filter_upwards [hV.mem_nhds ⟨hz₀Γ, hind z₀ hz₀⟩] with z hzV
        exact hHV z hzV.1 hzV.2
      exact heq.differentiableAt_iff.mpr
        (hh₁.differentiableAt (Γ.isOpen_compl_range.mem_nhds hz₀Γ))
  obtain ⟨R, hR, hball, hRind⟩ := Γ.exists_pos_index_eq_zero_outside_ball hΓ 0
  obtain ⟨L, hL0, hL⟩ := Γ.exists_norm_integral_le (F := F) hΓ
  obtain ⟨M₀, hM₀⟩ := Γ.isCompact_range.exists_bound_of_continuousOn (hf.continuousOn.mono hΓU)
  set M := max M₀ 0
  have hM : ∀ w ∈ Γ.range, ‖f w‖ ≤ M := fun w hw ↦ (hM₀ w hw).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  have hdecay : ∀ z : ℂ, R < ‖z‖ → ‖H z‖ ≤ L * (M / (‖z‖ - R)) := by
    intro z hzR
    have hzb : z ∉ ball 0 R := by simpa using hzR.le
    have hzΓ : z ∉ Γ.range := fun hm ↦ hzb (hball hm)
    rw [hHV z hzΓ (hRind z hzb)]
    refine hL _ _ fun w hw ↦ ?_
    have hwR : ‖w‖ < R := by simpa using hball hw
    have hpos : 0 < ‖z‖ - R := by linarith
    have hwz : ‖z‖ - R ≤ ‖w - z‖ := by
      calc ‖z‖ - R ≤ ‖z‖ - ‖w‖ := by linarith
        _ ≤ ‖w - z‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le z w
    rw [norm_smul, norm_inv, div_eq_inv_mul]
    exact mul_le_mul (inv_anti₀ hpos hwz) (hM w hw) (norm_nonneg _) (inv_nonneg.mpr hpos.le)
  have hlim : Tendsto (fun t : ℝ ↦ L * (M / (t - R))) atTop (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ ↦ t - R) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    simpa [div_eq_mul_inv] using (ht.inv_tendsto_atTop.const_mul M).const_mul L
  have hH : Tendsto H (cocompact ℂ) (𝓝 0) := by
    have hn := tendsto_norm_cocompact_atTop (E := ℂ)
    refine squeeze_zero_norm' ?_ (hlim.comp hn)
    filter_upwards [hn.eventually_gt_atTop R] with z hz using hdecay z hz
  have := hHdiff.apply_eq_of_tendsto_cocompact z hH
  rwa [hHU z hz] at this

/-- **Cauchy's integral formula for cycles.** For a `C¹` cycle in an open set `U` whose index
vanishes outside `U`, and a Banach-valued function holomorphic on `U`, the Cauchy integral at a
point of `U` off the cycle is the index times the value. -/
theorem integral_sub_inv_smul_eq_index_smul {U : Set ℂ} (hU : IsOpen U) (hΓ : Γ.IsC1)
    (hΓU : Γ.range ⊆ U) (hind : ∀ w, w ∉ U → Γ.index w = 0)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) (hzΓ : z ∉ Γ.range) :
    Γ.integral (fun w ↦ toSpanSingleton ℂ ((w - z)⁻¹ • f w)) =
      (2 * (Real.pi : ℂ) * Complex.I * Γ.index z) • f z := by
  have h := Γ.integral_dslope_eq_sub hΓ hΓU hf.continuousOn hzΓ
  rw [Γ.integral_dslope_eq_zero hU hΓ hΓU hind hf hz] at h
  exact (sub_eq_zero.mp h.symm)

/-- **Cauchy's theorem for cycles.** For a `C¹` cycle in an open set `U` whose index vanishes
outside `U`, the integral of every Banach-valued function holomorphic on `U` vanishes. -/
theorem integral_eq_zero {U : Set ℂ} (hU : IsOpen U) (hΓ : Γ.IsC1)
    (hΓU : Γ.range ⊆ U) (hind : ∀ w, w ∉ U → Γ.index w = 0)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) :
    Γ.integral (fun w ↦ toSpanSingleton ℂ (f w)) = 0 := by
  rcases isEmpty_or_nonempty (Fin Γ.n) with hn | hne
  · simp [Cycle.integral]
  · obtain ⟨i⟩ := hne
    set z₀ := (Γ.loop i).1
    have hz₀ : z₀ ∈ U := by
      have := hΓU (Γ.loop_mem_range i 0)
      simpa [z₀] using this
    have hg : DifferentiableOn ℂ (fun w ↦ (w - z₀) • f w) U :=
      (differentiableOn_id.sub_const z₀).smul hf
    have key := Γ.integral_dslope_eq_zero hU hΓ hΓU hind hg hz₀
    rw [← key]
    refine Γ.integral_congr fun w hw ↦ ?_
    congr 1
    by_cases hwz : w = z₀
    · rw [hwz, dslope_same]
      have hd := ((hasDerivAt_id z₀).sub_const z₀).smul
        (hf.differentiableAt (hU.mem_nhds hz₀)).hasDerivAt
      have hd' : HasDerivAt (fun w ↦ (w - z₀) • f w)
          ((id z₀ - z₀) • deriv f z₀ + (1 : ℂ) • f z₀) z₀ := hd
      rw [hd'.deriv]
      simp
    · rw [dslope_of_ne _ (Ne.symm hwz), slope_def_module, sub_self, zero_smul, zero_sub,
        smul_neg, smul_smul]
      have hmul : (z₀ - w)⁻¹ * (w - z₀) = -1 := by
        rw [← neg_sub z₀ w, mul_neg, inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hwz))]
      rw [hmul, neg_one_smul, neg_neg]

end Cycle

end Complex

end
