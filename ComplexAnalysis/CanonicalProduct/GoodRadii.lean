/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CanonicalProduct
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Good radii for canonical products

If `∑ ‖a i‖⁻¹ ^ (k + 1) < ∞`, the discs of radius `‖a i‖⁻¹ ^ (k + 1)` around the `a i` meet
the set of radii in a set of finite total length, so there are arbitrarily large `r` such that
the circle `‖z‖ = r` stays at distance at least `‖a i‖⁻¹ ^ (k + 1)` from every `a i`. This is
the circle on which the lower bound for the canonical product is applied in Hadamard's theorem.

## Main results

* `Complex.frequently_forall_norm_sub_ge`: arbitrarily large good radii.

## References

* E. M. Stein and R. Shakarchi, *Complex Analysis*, Chapter 5, Lemma 5.6.
-/

public noncomputable section

open Set Metric Filter Function MeasureTheory
open scoped Topology ENNReal

namespace Complex

variable {ι : Type*} {a : ι → ℂ} {k : ℕ}

/-- **Good radii.** If `∑ ‖a i‖⁻¹ ^ (k + 1) < ∞`, there are arbitrarily large `r` such that
every point of the circle `‖z‖ = r` is at distance at least `‖a i‖⁻¹ ^ (k + 1)` from every
`a i`. -/
theorem frequently_forall_norm_sub_ge (ha : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ ‖a i‖⁻¹ ^ (k + 1)) :
    ∃ᶠ r in atTop, ∀ z : ℂ, ‖z‖ = r → ∀ i, ‖a i‖⁻¹ ^ (k + 1) ≤ ‖z - a i‖ := by
  classical
  set δ : ι → ℝ := fun i ↦ ‖a i‖⁻¹ ^ (k + 1)
  have hδ0 : ∀ i, 0 ≤ δ i := fun i ↦ by positivity
  -- the index type is countable
  have hcount : Countable ι := by
    have h := hs.countable_support
    have hsupp : support (fun i ↦ ‖a i‖⁻¹ ^ (k + 1)) = univ := by
      ext i
      simp only [mem_support, mem_univ, iff_true]
      exact pow_ne_zero _ (inv_ne_zero (norm_ne_zero_iff.mpr (ha i)))
    rw [hsupp] at h
    exact Set.countable_univ_iff.mp h
  rw [Filter.frequently_atTop]
  intro L₀
  -- a finite set of indices outside of which the total length is less than one
  have htail := tendsto_tsum_compl_atTop_zero (fun i ↦ 2 * δ i)
  obtain ⟨s₀, hs₀⟩ := (htail.eventually (gt_mem_nhds one_pos)).exists
  -- a level above the finitely many exceptional discs
  set L₁ : ℝ := (∑ i ∈ s₀, (‖a i‖ + δ i)) + 1 with hL₁_def
  have hL₁ : ∀ i ∈ s₀, ‖a i‖ + δ i < L₁ := fun i hi ↦ by
    have := Finset.single_le_sum (f := fun i ↦ ‖a i‖ + δ i)
      (fun j _ ↦ add_nonneg (norm_nonneg _) (hδ0 j)) hi
    rw [hL₁_def]
    linarith
  set L : ℝ := max (max L₀ 1) L₁
  have hL0 : L₀ ≤ L := (le_max_left _ _).trans (le_max_left _ _)
  have hL1 : 1 ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  have hLL₁ : L₁ ≤ L := le_max_right _ _
  -- the bad radii outside `s₀` have measure less than `L`
  set B : Set ℝ := ⋃ i : {i // i ∉ s₀}, Icc (‖a i‖ - δ i) (‖a i‖ + δ i)
  have hB : volume B < ENNReal.ofReal L := by
    calc volume B ≤ ∑' i : {i // i ∉ s₀}, volume (Icc (‖a i‖ - δ i) (‖a i‖ + δ i)) :=
          measure_iUnion_le _
      _ = ∑' i : {i // i ∉ s₀}, ENNReal.ofReal (2 * δ i) := by
          refine tsum_congr fun i ↦ ?_
          rw [Real.volume_Icc]
          congr 1
          ring
      _ = ENNReal.ofReal (∑' i : {i // i ∉ s₀}, 2 * δ i) :=
          (ENNReal.ofReal_tsum_of_nonneg (f := fun i : {i // i ∉ s₀} ↦ 2 * δ i)
            (fun i ↦ mul_nonneg zero_le_two (hδ0 i)) ((hs.mul_left 2).subtype _)).symm
      _ < ENNReal.ofReal 1 := (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr hs₀
      _ ≤ ENNReal.ofReal L := ENNReal.ofReal_le_ofReal hL1
  have hnot : ¬ Icc L (2 * L) ⊆ B := by
    intro hsub
    have := measure_mono (μ := volume) hsub
    rw [Real.volume_Icc, show 2 * L - L = L by ring] at this
    exact absurd (this.trans_lt hB) (lt_irrefl _)
  obtain ⟨r, hr, hrB⟩ := Set.not_subset.mp hnot
  refine ⟨r, hL0.trans hr.1, fun z hz i ↦ ?_⟩
  have hnorm : |‖z‖ - ‖a i‖| ≤ ‖z - a i‖ := abs_norm_sub_norm_le z (a i)
  rw [hz] at hnorm
  refine le_trans ?_ hnorm
  by_cases hi : i ∈ s₀
  · have h1 := hL₁ i hi
    have h2 : ‖a i‖ + δ i < r := by linarith [hr.1]
    rw [abs_of_pos (by linarith [hδ0 i])]
    linarith
  · have hri : r ∉ Icc (‖a i‖ - δ i) (‖a i‖ + δ i) := fun h ↦
      hrB (mem_iUnion.mpr ⟨⟨i, hi⟩, h⟩)
    rw [mem_Icc, not_and_or, not_le, not_le] at hri
    rcases hri with h | h
    · rw [abs_of_neg (by linarith [hδ0 i])]
      linarith
    · rw [abs_of_pos (by linarith [hδ0 i])]
      linarith

end Complex

end
