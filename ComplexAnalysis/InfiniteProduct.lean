/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Analytic.Order

/-!
# Infinite products of holomorphic functions

For holomorphic functions `f i` on an open set `U` with summable uniform bounds on every compact
subset, the product `∏' i, (1 + f i z)` is holomorphic on `U` (Mathlib supplies the locally
uniform convergence), vanishes exactly where a factor vanishes, and its order of vanishing at a
point is the sum of the orders of the finitely many factors vanishing there.

## Main results

* `Complex.differentiableOn_tprod_one_add`: holomorphy of the product.
* `Complex.tprod_one_add_eq_zero_iff`: the zeros of the product.
* `Complex.analyticOrderAt_tprod_one_add`: the order of the product at a point.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorem VII.5.9.
-/

@[expose] public noncomputable section

open Set Metric Filter Function
open scoped Topology

namespace Complex

variable {ι : Type*} {U : Set ℂ} {f : ι → ℂ → ℂ}

/-- Summable uniform bounds on every compact subset of `U`: the hypothesis of the product
theorems. -/
def HasSummableBoundOn (f : ι → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧ ∀ᶠ i in cofinite, ∀ z ∈ K, ‖f i z‖ ≤ u i

/-- A summable uniform bound remains valid after restricting the domain. -/
theorem HasSummableBoundOn.mono {V : Set ℂ} (h : HasSummableBoundOn f U) (hVU : V ⊆ U) :
    HasSummableBoundOn f V :=
  fun K hKV hK ↦ h K (hKV.trans hVU) hK

/-- A subfamily inherits a summable uniform bound from the original family. -/
theorem HasSummableBoundOn.comp_subtype (h : HasSummableBoundOn f U) (p : ι → Prop) :
    HasSummableBoundOn (fun i : Subtype p ↦ f i) U := by
  intro K hKU hK
  obtain ⟨u, hu, hb⟩ := h K hKU hK
  exact ⟨fun i ↦ u i, hu.subtype p, Subtype.val_injective.tendsto_cofinite.eventually hb⟩

/-- Pointwise summability of the norms of the terms. -/
theorem HasSummableBoundOn.summable_norm (h : HasSummableBoundOn f U) {z : ℂ} (hz : z ∈ U) :
    Summable fun i ↦ ‖f i z‖ := by
  obtain ⟨u, hu, hb⟩ := h {z} (singleton_subset_iff.mpr hz) isCompact_singleton
  refine Summable.of_norm_bounded_eventually hu ?_
  filter_upwards [hb] with i hi
  simpa using hi z rfl

/-- The product converges locally uniformly on `U`. -/
theorem hasProdLocallyUniformlyOn_one_add (hU : IsOpen U) (hf : ∀ i, ContinuousOn (f i) U)
    (hb : HasSummableBoundOn f U) :
    HasProdLocallyUniformlyOn (fun i z ↦ 1 + f i z) (fun z ↦ ∏' i, (1 + f i z)) U := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hU
  intro K hKU hK
  obtain ⟨u, hu, h⟩ := hb K hKU hK
  exact Summable.hasProdUniformlyOn_one_add hK hu h fun i ↦ (hf i).mono hKU

/-- **Holomorphy of infinite products.** -/
theorem differentiableOn_tprod_one_add (hU : IsOpen U) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hb : HasSummableBoundOn f U) :
    DifferentiableOn ℂ (fun z ↦ ∏' i, (1 + f i z)) U := by
  have h := hasProdLocallyUniformlyOn_one_add hU (fun i ↦ (hf i).continuousOn) hb
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  refine h.differentiableOn (Eventually.of_forall fun s ↦ ?_) hU
  have : (fun z ↦ ∏ i ∈ s, (1 + f i z)) = ∏ i ∈ s, (fun z ↦ 1 + f i z) := by
    ext z
    simp [Finset.prod_apply]
  rw [this]
  exact DifferentiableOn.finsetProd fun i _ ↦ (differentiableOn_const 1).add (hf i)

/-- **Zeros of infinite products.** The product vanishes exactly where a factor vanishes. -/
theorem tprod_one_add_eq_zero_iff (hb : HasSummableBoundOn f U) {z : ℂ} (hz : z ∈ U) :
    ∏' i, (1 + f i z) = 0 ↔ ∃ i, 1 + f i z = 0 := by
  classical
  have hsum := hb.summable_norm hz
  constructor
  · intro h
    by_contra hne
    push Not at hne
    exact tprod_one_add_ne_zero_of_summable hne hsum h
  · rintro ⟨i, hi⟩
    have hmul : ∀ (s : Set ι), Multipliable ((fun j ↦ 1 + f j z) ∘ (Subtype.val : s → ι)) :=
      fun s ↦ multipliable_one_add_of_summable (f := fun j : s ↦ f j z) (hsum.subtype _)
    rw [← Multipliable.tprod_mul_tprod_compl (s := (({i} : Finset ι) : Set ι)) (hmul _) (hmul _)]
    have h1 : (∏' x : ↥((({i} : Finset ι)) : Set ι), (1 + f x z)) =
        ∏ x ∈ ({i} : Finset ι), (1 + f x z) :=
      Finset.tprod_subtype ({i} : Finset ι) (fun j ↦ 1 + f j z)
    rw [h1, Finset.prod_singleton, hi, zero_mul]

/-- Only finitely many factors vanish at a point. -/
theorem finite_setOf_one_add_eq_zero (hb : HasSummableBoundOn f U) {z : ℂ} (hz : z ∈ U) :
    {i | 1 + f i z = 0}.Finite := by
  have hsum := hb.summable_norm hz
  have h := hsum.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun i hi ↦ ?_
  have hi' : 1 + f i z = 0 := hi
  have : f i z = -1 := by linear_combination hi'
  change ¬ ‖f i z‖ < 1
  rw [this]
  simp

/-- The order of a finite product of analytic functions is the sum of the orders. -/
theorem analyticOrderAt_finset_prod {s : Finset ι} {g : ι → ℂ → ℂ} {a : ℂ}
    (hg : ∀ i ∈ s, AnalyticAt ℂ (g i) a) :
    analyticOrderAt (fun z ↦ ∏ i ∈ s, g i z) a = ∑ i ∈ s, analyticOrderAt (g i) a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact (analyticAt_const.analyticOrderAt_eq_zero).mpr one_ne_zero
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    have h1 : AnalyticAt ℂ (g i) a := hg i (Finset.mem_insert_self i s)
    have h2 : AnalyticAt ℂ (fun z ↦ ∏ j ∈ s, g j z) a :=
      Finset.analyticAt_fun_prod _ fun j hj ↦ hg j (Finset.mem_insert_of_mem hj)
    rw [← ih fun j hj ↦ hg j (Finset.mem_insert_of_mem hj)]
    exact analyticOrderAt_mul (f := g i) (g := fun z ↦ ∏ j ∈ s, g j z) h1 h2

/-- **Orders of infinite products.** The order of the product at a point of `U` is the sum
of the orders of the factors vanishing there. -/
theorem analyticOrderAt_tprod_one_add (hU : IsOpen U) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hb : HasSummableBoundOn f U) {a : ℂ} (ha : a ∈ U) :
    analyticOrderAt (fun z ↦ ∏' i, (1 + f i z)) a =
      ∑ i ∈ (finite_setOf_one_add_eq_zero hb ha).toFinset,
        analyticOrderAt (fun z ↦ 1 + f i z) a := by
  classical
  set N : Finset ι := (finite_setOf_one_add_eq_zero hb ha).toFinset
  have hNmem : ∀ i, i ∈ N ↔ 1 + f i a = 0 := fun i ↦ by
    simp [N, Set.Finite.mem_toFinset]
  -- the product of the vanishing factors and the product of the others
  set F : ℂ → ℂ := fun z ↦ ∏ i ∈ N, (1 + f i z)
  set Q : ℂ → ℂ := fun z ↦ ∏' i : ↥((N : Set ι)ᶜ), (1 + f i z)
  have hsplit : ∀ z ∈ U, ∏' i, (1 + f i z) = F z * Q z := by
    intro z hz
    have hsum := hb.summable_norm hz
    have hmul : ∀ (s : Set ι), Multipliable ((fun j ↦ 1 + f j z) ∘ (Subtype.val : s → ι)) :=
      fun s ↦ multipliable_one_add_of_summable (f := fun j : s ↦ f j z) (hsum.subtype _)
    rw [← Multipliable.tprod_mul_tprod_compl (s := (N : Set ι)) (hmul _) (hmul _)]
    congr 1
    exact Finset.tprod_subtype N fun i ↦ 1 + f i z
  have hFan : AnalyticAt ℂ F a :=
    Finset.analyticAt_fun_prod _ fun i _ ↦
      (analyticAt_const.add ((hf i).analyticOnNhd hU a ha))
  have hQdiff : DifferentiableOn ℂ Q U :=
    differentiableOn_tprod_one_add hU (fun i ↦ hf i) (hb.comp_subtype _)
  have hQan : AnalyticAt ℂ Q a := (hQdiff.analyticOnNhd hU) a ha
  have hQne : Q a ≠ 0 := by
    have hsum := (hb.comp_subtype fun i ↦ i ∈ (N : Set ι)ᶜ).summable_norm ha
    refine tprod_one_add_ne_zero_of_summable (fun i ↦ ?_) hsum
    have hi := i.2
    rw [mem_compl_iff, Finset.mem_coe, hNmem] at hi
    exact hi
  have hev : (fun z ↦ ∏' i, (1 + f i z)) =ᶠ[𝓝 a] fun z ↦ F z * Q z := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hsplit z hz
  rw [analyticOrderAt_congr hev]
  change analyticOrderAt (F * Q) a = _
  rw [analyticOrderAt_mul hFan hQan, (hQan.analyticOrderAt_eq_zero).mpr hQne, add_zero]
  exact analyticOrderAt_finset_prod fun i _ ↦ analyticAt_const.add ((hf i).analyticOnNhd hU a ha)

end Complex

end
