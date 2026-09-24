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
  have hcont : ContinuousOn (fun p : ℂ × ℂ => (p.1 - p.2)⁻¹) (Ω ×ˢ K) := by
    refine (continuous_fst.sub continuous_snd).continuousOn.inv₀ ?_
    rintro ⟨w, z⟩ ⟨hw, hz⟩
    exact sub_ne_zero.mpr fun h => hdisj.notMem_of_mem_left hw (h ▸ hz)
  have huc := (hΩ.prod hK).uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, h⟩ := huc η hη
  refine ⟨δ, hδ, fun w hw w' hw' z hz hd => ?_⟩
  have := h (w, z) ⟨hw, hz⟩ (w', z) ⟨hw', hz⟩ (by
    rw [Prod.dist_eq, dist_self]
    simpa using hd)
  rw [dist_eq_norm] at this
  exact this.le

/-- **Finite pole sums approximate Cauchy-type integrals.** Let `Ω` and `K` be disjoint compact
sets and `g` a function bounded by `C` on `Ω` and integrable on `Ω`. For every `ε > 0` there
are finitely many poles `c i ∈ Ω` and coefficients `a i` such that the Cauchy-type integral
`∫ w in Ω, g w * (w - z)⁻¹` is within `ε` of `∑ i, a i * (c i - z)⁻¹` for every `z ∈ K`. -/
theorem exists_finset_approx_setIntegral_inv_sub {Ω K : Set ℂ} (hΩ : IsCompact Ω)
    (hK : IsCompact K) (hdisj : Disjoint Ω K) {g : ℂ → ℂ} (hg : IntegrableOn g Ω)
    {C : ℝ} (hC : ∀ w ∈ Ω, ‖g w‖ ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℂ), (∀ i, c i ∈ Ω) ∧
      ∀ z ∈ K, ‖(∫ w in Ω, g w * (w - z)⁻¹) - ∑ i, a i * (c i - z)⁻¹‖ ≤ ε := by
  classical
  set C' : ℝ := max C 0 with hC'_def
  have hC' : ∀ w ∈ Ω, ‖g w‖ ≤ C' := fun w hw => (hC w hw).trans (le_max_left _ _)
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set V : ℝ := (volume Ω).toReal with hV_def
  have hVfin : volume Ω ≠ ⊤ := hΩ.measure_lt_top.ne
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set η : ℝ := ε / (C' * V + 1) with hη_def
  have hη : 0 < η := div_pos hε (by positivity)
  have hηbound : C' * η * V ≤ ε := by
    have h1 : C' * η * V = η * (C' * V) := by ring
    rw [h1, hη_def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hC'0 hV0]
  obtain ⟨δ, hδ, hker⟩ := exists_delta_inv_sub_kernel hΩ hK hdisj hη
  obtain ⟨t, htΩ, htfin, hcover⟩ := finite_cover_balls_of_compact hΩ hδ
  set l : List ℂ := htfin.toFinset.toList with hl_def
  set n : ℕ := l.length with hn_def
  have hmem_l : ∀ x ∈ t, x ∈ l := fun x hx => by
    simp [l, Finset.mem_toList, htfin.mem_toFinset, hx]
  have hl_mem : ∀ x ∈ l, x ∈ Ω := fun x hx => by
    apply htΩ
    simpa [l, Finset.mem_toList, htfin.mem_toFinset] using hx
  set c : Fin n → ℂ := fun i => l.get i with hc_def
  have hcΩ : ∀ i, c i ∈ Ω := fun i => hl_mem _ (List.get_mem l i)
  -- the pieces of the cover
  set f : ℕ → Set ℂ := fun k => if h : k < n then ball (c ⟨k, h⟩) δ ∩ Ω else ∅ with hf_def
  have hf_of_lt : ∀ i : Fin n, f i = ball (c i) δ ∩ Ω := fun i => by
    simp only [f]
    split_ifs with h
    · rfl
    · exact absurd i.isLt h
  have hfmeas : ∀ k, MeasurableSet (f k) := by
    intro k
    simp only [f]
    split_ifs
    · exact measurableSet_ball.inter hΩ.measurableSet
    · exact MeasurableSet.empty
  have hfΩ : ∀ k, f k ⊆ Ω := by
    intro k
    simp only [f]
    split_ifs
    · exact inter_subset_right
    · exact empty_subset _
  have hfcover : Ω ⊆ ⋃ k, f k := by
    intro w hw
    obtain ⟨x, hxt, hwx⟩ := mem_iUnion₂.mp (hcover hw)
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (hmem_l x hxt)
    refine mem_iUnion.mpr ⟨i, ?_⟩
    rw [hf_of_lt i]
    exact ⟨(show c i = x from hi) ▸ hwx, hw⟩
  set D : ℕ → Set ℂ := disjointed f with hD_def
  have hDmeas : ∀ k, MeasurableSet (D k) := MeasurableSet.disjointed hfmeas
  have hDdisj : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed f
  have hDsub : ∀ k, D k ⊆ f k := disjointed_subset f
  have hDΩ : ∀ k, D k ⊆ Ω := fun k => (hDsub k).trans (hfΩ k)
  have hDunion : (⋃ k, D k) = Ω := by
    apply Subset.antisymm (iUnion_subset hDΩ)
    rw [hD_def, iUnion_disjointed]
    exact hfcover
  have hDempty : ∀ k, n ≤ k → D k = ∅ := by
    intro k hk
    apply eq_empty_of_subset_empty
    refine (hDsub k).trans ?_
    simp [f, not_lt.mpr hk]
  have hDfin : ∀ k, volume (D k) ≠ ⊤ := fun k =>
    ((measure_mono (hDΩ k)).trans_lt hΩ.measure_lt_top).ne
  -- coefficients
  refine ⟨n, c, fun i => ∫ w in D i, g w, hcΩ, fun z hz => ?_⟩
  have hkc : ContinuousOn (fun w => (w - z)⁻¹) Ω :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun w hw =>
      sub_ne_zero.mpr fun h => hdisj.notMem_of_mem_left hw ((show w = z from h) ▸ hz)
  have hint : IntegrableOn (fun w => g w * (w - z)⁻¹) Ω := hg.mul_continuousOn hkc hΩ
  -- split the integral over the pieces
  have hsplit : ∫ w in Ω, g w * (w - z)⁻¹ = ∑ i : Fin n, ∫ w in D i, g w * (w - z)⁻¹ := by
    rw [← hDunion, integral_iUnion hDmeas hDdisj (hDunion ▸ hint)]
    rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
      rw [hDempty k (by simpa using hk)]
      simp), Finset.sum_range]
  have hsplit' : ∑ i : Fin n, (∫ w in D i, g w) * (c i - z)⁻¹ =
      ∑ i : Fin n, ∫ w in D i, g w * (c i - z)⁻¹ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const]
  rw [hsplit, hsplit', ← Finset.sum_sub_distrib]
  have hsub : ∀ i : Fin n, (∫ w in D i, g w * (w - z)⁻¹) - ∫ w in D i, g w * (c i - z)⁻¹ =
      ∫ w in D i, g w * ((w - z)⁻¹ - (c i - z)⁻¹) := by
    intro i
    rw [← integral_sub (hint.mono_set (hDΩ i))
      ((hg.mono_set (hDΩ i)).mul_const _)]
    exact integral_congr_ae (Eventually.of_forall fun w => by ring)
  simp_rw [hsub]
  refine (norm_sum_le _ _).trans ?_
  have hpiece : ∀ i : Fin n, ‖∫ w in D i, g w * ((w - z)⁻¹ - (c i - z)⁻¹)‖ ≤
      C' * η * (volume (D i)).toReal := by
    intro i
    refine norm_setIntegral_le_of_norm_le_const (hDfin i).lt_top fun w hw => ?_
    have hwf := hDsub i hw
    rw [hf_of_lt i] at hwf
    have hwΩ : w ∈ Ω := hwf.2
    have hwc : dist w (c i) < δ := mem_ball.mp hwf.1
    rw [norm_mul]
    exact mul_le_mul (hC' w hwΩ) (hker w hwΩ (c i) (hcΩ i) z hz hwc) (norm_nonneg _) hC'0
  refine (Finset.sum_le_sum fun i _ => hpiece i).trans ?_
  rw [← Finset.mul_sum]
  have hvol : ∑ i : Fin n, (volume (D i)).toReal = V := by
    rw [hV_def, ← hDunion, measure_iUnion hDdisj hDmeas,
      tsum_eq_sum (s := Finset.range n) (fun k hk => by rw [hDempty k (by simpa using hk)]; simp),
      ENNReal.toReal_sum (fun k _ => hDfin k), Finset.sum_range]
  rw [hvol]
  exact hηbound

end Complex

end
