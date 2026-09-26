/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Rouche

/-!
# The local mapping theorem

If `f` is analytic at `a` and `f - f a` vanishes to order `m ≥ 1` at `a`, then `f` is locally
`m`-to-one near `a`: for every small `ε` there is `δ > 0` such that every value `w` with
`0 < ‖w - f a‖ < δ` is taken exactly `m` times in `ball a ε`, each time with nonzero derivative.
The proof is Rouché's theorem: the divisor degrees of `f - w` and `f - f a` on the closed disc
agree, the latter is `m`, and the zeros of `f - w` are simple because `deriv f` does not vanish
on a punctured neighborhood of `a`.

## Main results

* `Complex.eventually_ne_and_deriv_ne_zero`: `f - f a` and `deriv f` vanish nowhere on a
  punctured neighborhood of `a` when the order is finite.
* `Complex.exists_forall_ncard_preimage_eq`: **the local mapping theorem**.

## References

* B. Simon, *Basic Complex Analysis*, Theorem 3.4.1.
* J. B. Conway, *Functions of One Complex Variable I*, Theorem IV.7.4 (proof).
-/

public noncomputable section

open Set Metric Filter Function MeromorphicOn
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
exactly `m` preimages in `ball a ε`, all with nonzero derivative. -/
theorem exists_forall_ncard_preimage_eq (hf : AnalyticAt ℂ f a) {m : ℕ}
    (hord : analyticOrderAt (fun z ↦ f z - f a) a = m) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ w, w ≠ f a → ‖w - f a‖ < δ →
      {z ∈ ball a ε | f z = w}.Finite ∧ {z ∈ ball a ε | f z = w}.ncard = m ∧
        ∀ z ∈ ball a ε, f z = w → deriv f z ≠ 0 := by
  classical
  have hne := eventually_ne_and_deriv_ne_zero hf (by rw [hord]; exact ENat.natCast_ne_top m)
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.mem_nhdsWithin_iff.mp hne
  obtain ⟨ε₂, hε₂, han⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
  refine ⟨min ε₁ ε₂ / 2, by positivity, fun ε hε hεle ↦ ?_⟩
  have hεε₁ : ε < ε₁ := by linarith [min_le_left ε₁ ε₂]
  have hεε₂ : ε < ε₂ := by linarith [min_le_right ε₁ ε₂]
  have hfan : AnalyticOnNhd ℂ f (closedBall a ε) := fun z hz ↦
    han (lt_of_le_of_lt (mem_closedBall.mp hz) hεε₂)
  have hpunct : ∀ z ∈ closedBall a ε, z ≠ a → f z ≠ f a ∧ deriv f z ≠ 0 := fun z hz hza ↦
    hball ⟨mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) hεε₁), hza⟩
  have hfa : AnalyticOnNhd ℂ (fun z ↦ f z - f a) (closedBall a ε) :=
    hfan.sub analyticOnNhd_const
  -- the minimum of `‖f - f a‖` on the sphere
  obtain ⟨b, hb, hmin⟩ := (isCompact_sphere a ε).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hε.le) (hfa.continuousOn.norm.mono sphere_subset_closedBall)
  have hbne : b ≠ a := by
    intro h
    rw [mem_sphere, h, dist_self] at hb
    exact hε.ne hb
  have hδ : 0 < ‖f b - f a‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (hpunct b (sphere_subset_closedBall hb) hbne).1)
  refine ⟨‖f b - f a‖, hδ, fun w hw hwδ ↦ ?_⟩
  have hfw : AnalyticOnNhd ℂ (fun z ↦ f z - w) (closedBall a ε) := hfan.sub analyticOnNhd_const
  -- Rouché's theorem
  have hsphere : ∀ z ∈ sphere a ε, ‖(f z - w) - (f z - f a)‖ < ‖f z - f a‖ := by
    intro z hz
    rw [show f z - w - (f z - f a) = -(w - f a) by ring, norm_neg]
    exact hwδ.trans_le (hmin hz)
  have hrouche := sum_divisor_eq_of_norm_sub_lt hε hfa hfw hsphere
  -- the divisor of `f - f a` has degree `m`
  have hdeg : (∑ᶠ z, divisor (fun z ↦ f z - f a) (closedBall a ε) z) = m := by
    rw [finsum_eq_single _ a]
    · rw [hfa.divisor_apply (mem_closedBall_self hε.le), hord]
      simp
    · intro z hz
      by_cases hzb : z ∈ closedBall a ε
      · rw [hfa.divisor_apply hzb]
        have : analyticOrderAt (fun z ↦ f z - f a) z = 0 :=
          ((hfan z hzb).sub analyticAt_const).analyticOrderAt_eq_zero.mpr
            (sub_ne_zero.mpr (hpunct z hzb hz).1)
        rw [this]
        simp
      · exact Function.notMem_support.mp fun h ↦ hzb ((divisor _ _).supportWithinDomain h)
  -- the zeros of `f - w` lie in the open disc, away from `a`, and are simple
  set Z := {z ∈ ball a ε | f z = w}
  have hZ' : ∀ z ∈ closedBall a ε, f z = w → z ∈ ball a ε := by
    intro z hz hfz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    rcases hz.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hsphere z (mem_sphere.mpr h)
      rw [hfz, sub_self, zero_sub, norm_neg] at this
      exact lt_irrefl _ this
  have hderiv : ∀ z ∈ ball a ε, f z = w → deriv f z ≠ 0 := by
    intro z hz hfz
    have hza : z ≠ a := fun h ↦ hw (by rw [← hfz, h])
    exact (hpunct z (ball_subset_closedBall hz) hza).2
  have hDval : ∀ z, divisor (fun z ↦ f z - w) (closedBall a ε) z = if z ∈ Z then 1 else 0 := by
    intro z
    by_cases hzb : z ∈ closedBall a ε
    · rw [hfw.divisor_apply hzb]
      by_cases hfz : f z = w
      · have hzZ : z ∈ Z := ⟨hZ' z hzb hfz, hfz⟩
        have h1 : analyticOrderAt (fun z ↦ f z - w) z = 1 := by
          refine ((hfan z hzb).sub analyticAt_const).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
            (by simp [hfz]) ?_
          have hdz : deriv (f - fun _ ↦ w) z = deriv f z := by
            change deriv (fun z ↦ f z - w) z = deriv f z
            exact deriv_sub_const w
          rw [hdz]
          exact hderiv z hzZ.1 hfz
        rw [h1]
        simp [hzZ]
      · have hzZ : z ∉ Z := fun h ↦ hfz h.2
        have h0 : analyticOrderAt (fun z ↦ f z - w) z = 0 :=
          ((hfan z hzb).sub analyticAt_const).analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hfz)
        rw [h0]
        simp [hzZ]
    · have hzZ : z ∉ Z := fun h ↦ hzb (ball_subset_closedBall h.1)
      rw [Function.notMem_support.mp fun h ↦ hzb ((divisor _ _).supportWithinDomain h)]
      simp [hzZ]
  have hsupp : support (divisor (fun z ↦ f z - w) (closedBall a ε)) = Z := by
    ext z
    rw [mem_support, hDval z]
    split_ifs with h <;> simp [h]
  have hZfin : Z.Finite := hsupp ▸ (divisor _ _).finiteSupport (isCompact_closedBall a ε)
  have hsum : (∑ᶠ z, divisor (fun z ↦ f z - w) (closedBall a ε) z) =
      (hZfin.toFinset.card : ℤ) := by
    rw [finsum_eq_sum_of_support_subset _ (s := hZfin.toFinset) (by rw [hsupp]; simp)]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    simp [hDval z, hZfin.mem_toFinset.mp hz]
  refine ⟨hZfin, ?_, hderiv⟩
  rw [Set.ncard_eq_toFinset_card Z hZfin]
  have : (hZfin.toFinset.card : ℤ) = m := by rw [← hsum, ← hrouche, hdeg]
  exact_mod_cast this

end Complex

end
