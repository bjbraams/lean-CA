/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Order.Disjointed

/-!
# Uniform approximation of Cauchy-type integrals by finite pole sums

For a compact set `Ω` and a compact set `K` disjoint from it, the Cauchy-type integral
`z ↦ ∫ w in Ω, g w * (w - z)⁻¹` of a bounded integrable density `g` is, uniformly on `K`, a
limit of finite sums `∑ i, a i * (c i - z)⁻¹` with poles `c i ∈ Ω`. The poles are the centers of
a finite cover of `Ω` by small balls, the coefficients are the integrals of `g` over the pieces
of a disjoint refinement of the cover, and the error is controlled by the uniform continuity of
the kernel on `Ω × K`.

This is the analytic core of Runge's approximation theorem (Conway VIII.1, Simon 4.7).

## Main results

* `Complex.exists_finset_approx_setIntegral_inv_sub`: the approximation statement.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set MeasureTheory Metric Filter
open scoped Topology

namespace Complex

/-- Uniform continuity of the Cauchy kernel `(w, z) ↦ (w - z)⁻¹` on a product of disjoint
compact sets. -/
theorem exists_delta_inv_sub_kernel {Ω K : Set ℂ} (hΩ : IsCompact Ω) (hK : IsCompact K)
    (hdisj : Disjoint Ω K) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ w ∈ Ω, ∀ w' ∈ Ω, ∀ z ∈ K, dist w w' < δ →
      ‖(w - z)⁻¹ - (w' - z)⁻¹‖ ≤ η := by
  have hcont : ContinuousOn (fun p : ℂ × ℂ ↦ (p.1 - p.2)⁻¹) (Ω ×ˢ K) := by
    refine (continuous_fst.sub continuous_snd).continuousOn.inv₀ ?_
    rintro ⟨w, z⟩ ⟨hw, hz⟩
    exact sub_ne_zero.mpr fun h ↦ hdisj.notMem_of_mem_left hw (h ▸ hz)
  have huc := (hΩ.prod hK).uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, h⟩ := huc η hη
  refine ⟨δ, hδ, fun w hw w' hw' z hz hd ↦ ?_⟩
  have := h (w, z) ⟨hw, hz⟩ (w', z) ⟨hw', hz⟩ (by
    rw [Prod.dist_eq, dist_self]
    simpa using hd)
  rw [dist_eq_norm] at this
  exact this.le

/-- **A finite partition of a compact set into small pieces.** A compact set `Ω` is the
disjoint union of finitely many measurable pieces `D i`, each contained in a ball of radius `δ`
about a point `c i ∈ Ω`. -/
theorem _root_.IsCompact.exists_finite_measurable_partition {Ω : Set ℂ} (hΩ : IsCompact Ω)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (D : Fin n → Set ℂ), (∀ i, c i ∈ Ω) ∧
      (∀ i, MeasurableSet (D i)) ∧ Pairwise (Function.onFun Disjoint D) ∧ (⋃ i, D i) = Ω ∧
      ∀ i, D i ⊆ ball (c i) δ ∩ Ω := by
  classical
  obtain ⟨t, htΩ, htfin, hcover⟩ := finite_cover_balls_of_compact hΩ hδ
  set l : List ℂ := htfin.toFinset.toList
  set n : ℕ := l.length
  set c : Fin n → ℂ := fun i ↦ l.get i
  have hl : ∀ x ∈ l, x ∈ t := fun x hx ↦ by simpa [l] using hx
  have hcΩ : ∀ i, c i ∈ Ω := fun i ↦ htΩ (hl _ (List.get_mem l i))
  -- the pieces of the cover, indexed by `ℕ`, and their disjoint refinement
  set f : ℕ → Set ℂ := fun k ↦ if h : k < n then ball (c ⟨k, h⟩) δ ∩ Ω else ∅
  have hf_of_lt : ∀ i : Fin n, f i = ball (c i) δ ∩ Ω := fun i ↦ by simp [f, i.isLt]
  have hfΩ : ∀ k, f k ⊆ Ω := fun k ↦ by
    simp only [f]
    split_ifs
    exacts [inter_subset_right, empty_subset _]
  have hfcover : Ω ⊆ ⋃ k, f k := by
    intro w hw
    obtain ⟨x, hxt, hwx⟩ := mem_iUnion₂.mp (hcover hw)
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (show x ∈ l by simp [l, hxt])
    exact mem_iUnion.mpr ⟨i, by rw [hf_of_lt i]; exact ⟨(show c i = x from hi) ▸ hwx, hw⟩⟩
  have hfempty : ∀ k, n ≤ k → f k = ∅ := fun k hk ↦ by simp [f, not_lt.mpr hk]
  have hDempty : ∀ k, n ≤ k → disjointed f k = ∅ := fun k hk ↦
    subset_empty_iff.mp ((disjointed_subset f k).trans (hfempty k hk).subset)
  refine ⟨n, c, fun i ↦ disjointed f i, hcΩ, fun i ↦ MeasurableSet.disjointed (fun k ↦ ?_) i,
    fun i j hij ↦ disjoint_disjointed f (Fin.val_injective.ne hij), ?_,
    fun i ↦ (disjointed_subset f i).trans (hf_of_lt i).subset⟩
  · simp only [f]
    split_ifs
    exacts [measurableSet_ball.inter hΩ.measurableSet, MeasurableSet.empty]
  · refine Subset.antisymm (iUnion_subset fun i ↦ (disjointed_subset f i).trans (hfΩ i)) ?_
    refine hfcover.trans (iUnion_disjointed (f := f) ▸ fun w hw ↦ ?_)
    obtain ⟨k, hk⟩ := mem_iUnion.mp hw
    have hkn : k < n := by
      by_contra h
      rw [hDempty k (not_lt.mp h)] at hk
      exact hk
    exact mem_iUnion.mpr ⟨⟨k, hkn⟩, hk⟩

/-- **Finite pole sums approximate Cauchy-type integrals.** Let `Ω` and `K` be disjoint compact
sets and `g` a function bounded by `C` on `Ω` and integrable on `Ω`. For every `ε > 0` there
are finitely many poles `c i ∈ Ω` and coefficients `a i` such that the Cauchy-type integral
`∫ w in Ω, g w * (w - z)⁻¹` is within `ε` of `∑ i, a i * (c i - z)⁻¹` for every `z ∈ K`. -/
theorem exists_finset_approx_setIntegral_inv_sub {Ω K : Set ℂ} (hΩ : IsCompact Ω)
    (hK : IsCompact K) (hdisj : Disjoint Ω K) {g : ℂ → ℂ} (hg : IntegrableOn g Ω)
    {C : ℝ} (hC : ∀ w ∈ Ω, ‖g w‖ ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℂ), (∀ i, c i ∈ Ω) ∧
      ∀ z ∈ K, ‖(∫ w in Ω, g w * (w - z)⁻¹) - ∑ i, a i * (c i - z)⁻¹‖ ≤ ε := by
  set C' : ℝ := max C 0
  have hC' : ∀ w ∈ Ω, ‖g w‖ ≤ C' := fun w hw ↦ (hC w hw).trans (le_max_left _ _)
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set V : ℝ := (volume Ω).toReal
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set η : ℝ := ε / (C' * V + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hηbound : C' * η * V ≤ ε := by
    rw [mul_right_comm, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hC'0 hV0]
  obtain ⟨δ, hδ, hker⟩ := exists_delta_inv_sub_kernel hΩ hK hdisj hη
  obtain ⟨n, c, D, hcΩ, hDmeas, hDdisj, hDunion, hDsub⟩ :=
    hΩ.exists_finite_measurable_partition hδ
  have hDΩ : ∀ i, D i ⊆ Ω := fun i ↦ (hDsub i).trans inter_subset_right
  have hDfin : ∀ i, volume (D i) ≠ ⊤ := fun i ↦
    ((measure_mono (hDΩ i)).trans_lt hΩ.measure_lt_top).ne
  refine ⟨n, c, fun i ↦ ∫ w in D i, g w, hcΩ, fun z hz ↦ ?_⟩
  have hkc : ContinuousOn (fun w ↦ (w - z)⁻¹) Ω :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦
      sub_ne_zero.mpr fun h ↦ hdisj.notMem_of_mem_left hw ((show w = z from h) ▸ hz)
  have hint : IntegrableOn (fun w ↦ g w * (w - z)⁻¹) Ω := hg.mul_continuousOn hkc hΩ
  -- split the integral over the pieces and compare each piece with its pole term
  have hsplit : ∫ w in Ω, g w * (w - z)⁻¹ = ∑ i, ∫ w in D i, g w * (w - z)⁻¹ := by
    rw [← hDunion, integral_iUnion hDmeas hDdisj (hDunion ▸ hint), tsum_fintype]
  have hpiece : ∀ i, ‖(∫ w in D i, g w * (w - z)⁻¹) - (∫ w in D i, g w) * (c i - z)⁻¹‖ ≤
      C' * η * (volume (D i)).toReal := by
    intro i
    rw [← integral_mul_const, ← integral_sub (hint.mono_set (hDΩ i))
      ((hg.mono_set (hDΩ i)).mul_const _)]
    refine norm_setIntegral_le_of_norm_le_const (hDfin i).lt_top fun w hw ↦ ?_
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (hC' w (hDΩ i hw)) (hker w (hDΩ i hw) (c i) (hcΩ i) z hz
      (mem_ball.mp (hDsub i hw).1)) (norm_nonneg _) hC'0
  have hvol : ∑ i, (volume (D i)).toReal = V := by
    have := measure_iUnion (μ := volume) hDdisj hDmeas
    rw [hDunion, tsum_fintype] at this
    rw [← ENNReal.toReal_sum fun i _ ↦ hDfin i, ← this]
  rw [hsplit, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ ↦ hpiece i).trans ?_)
  rw [← Finset.mul_sum, hvol]
  exact hηbound

end Complex

end
