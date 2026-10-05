/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Complex.Conformal.LocalDegree

/-!
# The local mapping theorem

If `f` is analytic at `a` and `f - f a` vanishes to order `m ≥ 1` at `a`, then `f` is locally
`m`-to-one near `a`: for every small `ε` there is `δ > 0` such that every value `w` with
`0 < ‖w - f a‖ < δ` is taken exactly `m` times in `ball a ε`, each time with nonzero derivative.
The counting statement adapts the Tau Ceti contributors' open-mapping degree
`TauCeti.localDegree_card` (`TauCeti.Analysis.Complex.Conformal.LocalDegree`), which is proved by
Rouché's theorem. The local input is that `f - f a` and `deriv f` do not vanish on a punctured
neighborhood of `a`, so the zeros of `f - w` are simple.

## Main results

* `Complex.eventually_ne_and_deriv_ne_zero`: `f - f a` and `deriv f` vanish nowhere on a
  punctured neighborhood of `a` when the order is finite.
* `Complex.exists_forall_ncard_preimage_eq`: **the local mapping theorem**.

## References

* B. Simon, *Basic Complex Analysis*, Theorem 3.4.1.
* J. B. Conway, *Functions of One Complex Variable I*, Theorem IV.7.4 (proof).
-/

public noncomputable section

open Set Metric Filter Function
open scoped Topology

namespace Complex

variable {f : ℂ → ℂ} {a : ℂ}

/-- Near a point where `f - f a` has finite order, neither `f - f a` nor `deriv f` vanishes on a
punctured neighborhood. -/
theorem eventually_ne_and_deriv_ne_zero (hf : AnalyticAt ℂ f a)
    (hord : analyticOrderAt (fun z ↦ f z - f a) a ≠ ⊤) :
    ∀ᶠ z in 𝓝[≠] a, f z ≠ f a ∧ deriv f z ≠ 0 := by
  have hg : AnalyticAt ℂ (fun z ↦ f z - f a) a := hf.sub analyticAt_const
  have h1 : ∀ᶠ z in 𝓝[≠] a, f z - f a ≠ 0 :=
    hg.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      fun h ↦ hord (analyticOrderAt_eq_top.mpr h)
  have hd : analyticOrderAt (deriv f) a ≠ ⊤ := by
    intro h
    have := hf.analyticOrderAt_deriv_add_one
    rw [h, top_add] at this
    exact hord this.symm
  have h2 : ∀ᶠ z in 𝓝[≠] a, deriv f z ≠ 0 :=
    hf.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      fun h ↦ hd (analyticOrderAt_eq_top.mpr h)
  filter_upwards [h1, h2] with z hz1 hz2
  exact ⟨sub_ne_zero.mp hz1, hz2⟩

/-- **The local mapping theorem.** If `f - f a` has order `m ≥ 1` at `a`, then for every
sufficiently small `ε` there is `δ > 0` such that every `w` with `0 < ‖w - f a‖ < δ` has
exactly `m` preimages in `ball a ε`, all with nonzero derivative.

This adapts the Tau Ceti contributors' `TauCeti.localDegree_card` from
`TauCeti.Analysis.Complex.Conformal.LocalDegree`; the counting argument is imported. -/
theorem exists_forall_ncard_preimage_eq (hf : AnalyticAt ℂ f a) {m : ℕ}
    (hord : analyticOrderAt (fun z ↦ f z - f a) a = m) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ w, w ≠ f a → ‖w - f a‖ < δ →
      {z ∈ ball a ε | f z = w}.Finite ∧ {z ∈ ball a ε | f z = w}.ncard = m ∧
        ∀ z ∈ ball a ε, f z = w → deriv f z ≠ 0 := by
  have hne := eventually_ne_and_deriv_ne_zero hf (by rw [hord]; exact ENat.natCast_ne_top m)
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.mem_nhdsWithin_iff.mp hne
  obtain ⟨ε₂, hε₂, han⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
  refine ⟨min ε₁ ε₂ / 2, by positivity, fun ε hε hεle ↦ ?_⟩
  have hεε₁ : ε < ε₁ := by linarith [min_le_left ε₁ ε₂]
  have hεε₂ : ε < ε₂ := by linarith [min_le_right ε₁ ε₂]
  have hpunct : ∀ z ∈ closedBall a ε, z ≠ a → f z ≠ f a ∧ deriv f z ≠ 0 := fun z hz hza ↦
    hball ⟨mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) hεε₁), hza⟩
  obtain ⟨δ, hδ, hcard⟩ := TauCeti.localDegree_card hε
    (fun z hz ↦ han (lt_of_le_of_lt (mem_closedBall.mp hz) hεε₂))
    (fun z hz hza ↦ (hpunct z hz hza).1)
    (fun z hz hza ↦ (hpunct z (ball_subset_closedBall hz) hza).2)
  refine ⟨δ, hδ, fun w hw hwδ ↦ ?_⟩
  obtain ⟨hfin, hn, -⟩ := hcard w hw hwδ
  refine ⟨hfin, by rw [hn, analyticOrderNatAt, hord, ENat.toNat_natCast], fun z hz hfz ↦ ?_⟩
  exact (hpunct z (ball_subset_closedBall hz) fun h ↦ hw (by rw [← hfz, h])).2

end Complex

end
