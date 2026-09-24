/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Cycle.Residue
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# The argument principle for cycles

For a `C¹` cycle `Γ` in an open set `U` whose index vanishes outside `U`, and a meromorphic
function `f` on `U` that is analytic and nonvanishing on the cycle, the integral of the
logarithmic derivative of `f` over the cycle is `2πi` times the sum of the indices of the
zeros and poles weighted by their orders. The sum is finite: the index vanishes outside a
compact subset of `U`, on which the divisor has finite support.

## Main results

* `Complex.Cycle.integral_logDeriv_eq_two_pi_I_mul_finsum`: the argument principle for cycles.
* `Complex.finite_diff_of_isCompact_of_mem_codiscreteWithin`: a set in the codiscrete filter of
  an open set has finite complement in every compact subset.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorem V.3.4.
-/

public noncomputable section

open Set MeasureTheory Metric Filter ContinuousLinearMap
open scoped unitInterval Topology

namespace Complex

/-- The complement of a set in the codiscrete filter of `U` meets every compact subset of `U`
in a finite set. -/
theorem finite_diff_of_isCompact_of_mem_codiscreteWithin {K U s : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) (hs : s ∈ codiscreteWithin U) : (K \ s).Finite := by
  rw [mem_codiscreteWithin] at hs
  have hev : ∀ x ∈ U, ∀ᶠ y in 𝓝[≠] x, y ∉ K \ s := fun x hx => by
    filter_upwards [disjoint_principal_right.mp (hs x hx)] with y hy hyK
    exact hy ⟨hKU hyK.1, hyK.2⟩
  have hclosed : IsClosed (K \ s) := by
    apply isClosed_of_closure_subset
    intro x hx
    have hxK : x ∈ K := hK.isClosed.closure_subset (closure_mono Set.sdiff_subset hx)
    by_contra hxT
    obtain ⟨t, ht, hts⟩ := (hev x (hKU hxK)).exists_mem
    obtain ⟨u, hu, hxu, hut⟩ := mem_nhdsWithin.mp ht
    obtain ⟨y, hyu, hyT⟩ := mem_closure_iff_nhds.mp hx u (hu.mem_nhds hxu)
    have hyx : y ≠ x := fun h => hxT (h ▸ hyT)
    exact hts y (hut ⟨hyu, hyx⟩) hyT
  refine (hK.of_isClosed_subset hclosed Set.sdiff_subset).finite ?_
  rw [isDiscrete_iff_discreteTopology, discreteTopology_subtype_iff]
  intro x hx
  rw [← disjoint_iff, disjoint_principal_right]
  exact hev x (hKU hx.1)

namespace Cycle

variable (Γ : Cycle)

/-- **The argument principle for cycles.** For a `C¹` cycle in an open set `U` whose index
vanishes outside `U`, and a meromorphic function on `U` which is not locally zero and is
analytic and nonvanishing on the cycle, the integral of the logarithmic derivative over the
cycle is `2πi` times the sum, over the zeros and poles, of the index times the order. -/
theorem integral_logDeriv_eq_two_pi_I_mul_finsum {U : Set ℂ} (hU : IsOpen U) (hΓ : Γ.IsC1)
    (hΓU : Γ.range ⊆ U) (hind : ∀ w, w ∉ U → Γ.index w = 0)
    {f : ℂ → ℂ} (hf : MeromorphicOn f U) (hne : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤)
    (hb : ∀ z ∈ Γ.range, AnalyticAt ℂ f z ∧ f z ≠ 0) :
    Γ.integral (fun z => toSpanSingleton ℂ (logDeriv f z)) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ∑ᶠ z, Γ.index z * (MeromorphicOn.divisor f U z : ℂ) := by
  classical
  obtain ⟨R, _, _, hRind⟩ := Γ.exists_pos_index_eq_zero_outside_ball hΓ 0
  set A : Set ℂ := {w | Γ.index w ≠ 0} with hA_def
  have hAball : A ⊆ ball 0 R := fun w hw => by
    by_contra h
    exact hw (hRind w h)
  set K : Set ℂ := closure A ∪ Γ.range with hK_def
  have hKc : IsCompact K :=
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (isBounded_ball.subset hAball).closure).union Γ.isCompact_range
  have hKU : K ⊆ U := by
    rintro w (hw | hw)
    · by_cases hwΓ : w ∈ Γ.range
      · exact hΓU hwΓ
      · by_contra hwU
        obtain ⟨r, hr, _, heq⟩ := Γ.exists_ball_index_eq hΓ hwΓ
        obtain ⟨v, hvball, hvA⟩ := mem_closure_iff_nhds.mp hw _ (ball_mem_nhds w hr)
        exact hvA ((heq v hvball).trans (hind w hwU))
    · exact hΓU hw
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hKc hU hKU
  have hVU' : V ⊆ U := subset_closure.trans hVU
  have hfV : MeromorphicOn f (closure V) := hf.mono_set hVU
  set D := MeromorphicOn.divisor f (closure V) with hD_def
  have hDfin : D.support.Finite := D.finiteSupport hVc
  have hAnfin : (closure V \ {x | AnalyticAt ℂ f x}).Finite :=
    finite_diff_of_isCompact_of_mem_codiscreteWithin hVc subset_rfl
      hfV.analyticAt_mem_codiscreteWithin
  set S : Finset ℂ := (hDfin.union hAnfin).toFinset with hS_def
  have hS : ∀ z, z ∈ (S : Set ℂ) ↔ z ∈ D.support ∨ z ∈ closure V \ {x | AnalyticAt ℂ f x} := by
    intro z
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, mem_union]
  have hSU : (S : Set ℂ) ⊆ U := by
    intro z hz
    rcases (hS z).mp hz with h | h
    · exact hVU (D.supportWithinDomain h)
    · exact hVU h.1
  have hΓV : Γ.range ⊆ V \ S := by
    intro z hz
    refine ⟨hKV (Or.inr hz), fun hzS => ?_⟩
    rcases (hS z).mp hzS with h | h
    · apply h
      rw [hD_def, MeromorphicOn.divisor_apply hfV (subset_closure (hKV (Or.inr hz))),
        (AnalyticAt.meromorphicNFAt (hb z hz).1).meromorphicOrderAt_eq_zero_iff.mpr (hb z hz).2]
      rfl
    · exact h.2 (hb z hz).1
  have hVind : ∀ w, w ∉ V → Γ.index w = 0 := by
    intro w hw
    by_contra h
    exact hw (hKV (Or.inl (subset_closure h)))
  have hlog : DifferentiableOn ℂ (logDeriv f) (V \ S) := by
    intro z hz
    have hzV : z ∈ closure V := subset_closure hz.1
    have han : AnalyticAt ℂ f z := by
      by_contra h
      exact hz.2 ((hS z).mpr (Or.inr ⟨hzV, h⟩))
    have hD0 : D z = 0 := by
      by_contra h
      exact hz.2 ((hS z).mpr (Or.inl h))
    have hord : meromorphicOrderAt f z = 0 := by
      have hne' := hne z (hVU hzV)
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne'
      rw [hD_def, MeromorphicOn.divisor_apply hfV hzV, ← hm] at hD0
      rw [← hm]
      simpa using hD0
    have hfz : f z ≠ 0 := (AnalyticAt.meromorphicNFAt han).meromorphicOrderAt_eq_zero_iff.mp hord
    exact (han.logDeriv hfz).differentiableAt.differentiableWithinAt
  rw [Γ.integral_eq_sum_index_smul_residue hVo S hΓ hΓV hVind hlog]
  have hres : ∀ a ∈ S, residue (logDeriv f) a = (MeromorphicOn.divisor f U a : ℂ) := by
    intro a ha
    have haU : a ∈ U := hSU (Finset.mem_coe.mpr ha)
    rw [residue_logDeriv (hf a haU) (hne a haU), MeromorphicOn.divisor_apply hf haU]
  rw [finsum_eq_sum_of_support_subset _ (s := S), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [hres a ha, smul_eq_mul, mul_assoc]
  · intro z hz
    rw [Function.mem_support] at hz
    have hzA : z ∈ A := fun h => hz (by simp [h])
    have hzU : z ∈ U := hKU (Or.inl (subset_closure hzA))
    have hzV : z ∈ closure V := subset_closure (hKV (Or.inl (subset_closure hzA)))
    apply (hS z).mpr
    left
    rw [Function.mem_support, hD_def, MeromorphicOn.divisor_apply hfV hzV]
    intro h0
    apply hz
    rw [MeromorphicOn.divisor_apply hf hzU, h0]
    simp

end Cycle

end Complex

end
