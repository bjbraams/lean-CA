/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Analytic continuation along paths

An analytic continuation along a continuous path `γ : I → ℂ` is a family of function elements
`(f t, ball (γ t) (r t))`, `f t` analytic on the disc, such that for `s` close to `t` the point
`γ s` lies in the disc of `t` and the elements `f s` and `f t` agree near `γ s`. The main result
is the **uniqueness of analytic continuation**: two continuations along the same path with the
same germ at the initial point have the same germ at the end point. The proof shows that the set
of parameters where the germs agree is clopen in the connected unit interval, using the identity
theorem on the discs.

## Main definitions

* `Complex.IsContinuationAlong γ f r`.

## Main results

* `Complex.IsContinuationAlong.eventuallyEq_one_of_eventuallyEq_zero`: uniqueness of the
  continuation along a path.
* `Complex.IsContinuationAlong.eventuallyEq_of_eventuallyEq`: the germs agree at every
  parameter.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Section IX.2 (Proposition 2.4).
* L. V. Ahlfors, *Complex Analysis*, Chapter 8, Section 1.
-/

public noncomputable section

open Set Metric Filter Function
open scoped Topology unitInterval

namespace Complex

/-- Compatible analytic function elements along a map `γ`: each `f t` is analytic on
`ball (γ t) (r t)`, and nearby elements agree near `γ s`. Continuity of `γ` is not part of
this predicate. -/
structure IsContinuationAlong (γ : I → ℂ) (f : I → ℂ → ℂ) (r : I → ℝ) : Prop where
  /-- The radii are positive. -/
  pos : ∀ t, 0 < r t
  /-- The function elements are analytic on their discs. -/
  analytic : ∀ t, AnalyticOnNhd ℂ (f t) (ball (γ t) (r t))
  /-- Nearby elements agree near the point of the path. -/
  compat : ∀ t, ∀ᶠ s in 𝓝 t, γ s ∈ ball (γ t) (r t) ∧ f s =ᶠ[𝓝 (γ s)] f t

namespace IsContinuationAlong

variable {γ : I → ℂ} {f g : I → ℂ → ℂ} {r ρ : I → ℝ}

/-- Two elements analytic on discs around `γ t` that agree near some point of the smaller disc
agree near `γ t`. -/
theorem eventuallyEq_center_of_eventuallyEq (hf : IsContinuationAlong γ f r)
    (hg : IsContinuationAlong γ g ρ) (t : I) {z : ℂ} (hz : z ∈ ball (γ t) (min (r t) (ρ t)))
    (h : f t =ᶠ[𝓝 z] g t) : f t =ᶠ[𝓝 (γ t)] g t := by
  have hball : ball (γ t) (min (r t) (ρ t)) ⊆ ball (γ t) (r t) :=
    ball_subset_ball (min_le_left _ _)
  have hball' : ball (γ t) (min (r t) (ρ t)) ⊆ ball (γ t) (ρ t) :=
    ball_subset_ball (min_le_right _ _)
  have heq : EqOn (f t) (g t) (ball (γ t) (min (r t) (ρ t))) :=
    ((hf.analytic t).mono hball).eqOn_of_preconnected_of_eventuallyEq
      ((hg.analytic t).mono hball') (convex_ball _ _).isPreconnected hz h
  have hmem : γ t ∈ ball (γ t) (min (r t) (ρ t)) := mem_ball_self (lt_min (hf.pos t) (hg.pos t))
  exact heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hmem)

/-- The set of parameters where two continuations agree is open. -/
theorem isOpen_setOf_eventuallyEq (hf : IsContinuationAlong γ f r)
    (hg : IsContinuationAlong γ g ρ) : IsOpen {t : I | f t =ᶠ[𝓝 (γ t)] g t} := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  filter_upwards [hf.compat t, hg.compat t] with s ⟨hsf, hsf'⟩ ⟨hsg, hsg'⟩
  have hball : ball (γ t) (min (r t) (ρ t)) ⊆ ball (γ t) (r t) :=
    ball_subset_ball (min_le_left _ _)
  have hball' : ball (γ t) (min (r t) (ρ t)) ⊆ ball (γ t) (ρ t) :=
    ball_subset_ball (min_le_right _ _)
  have heq : EqOn (f t) (g t) (ball (γ t) (min (r t) (ρ t))) :=
    ((hf.analytic t).mono hball).eqOn_of_preconnected_of_eventuallyEq
      ((hg.analytic t).mono hball') (convex_ball _ _).isPreconnected
      (mem_ball_self (lt_min (hf.pos t) (hg.pos t))) ht
  have hs : γ s ∈ ball (γ t) (min (r t) (ρ t)) := by
    rw [mem_ball, lt_min_iff]
    exact ⟨hsf, hsg⟩
  have hts : f t =ᶠ[𝓝 (γ s)] g t := heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hs)
  exact hsf'.trans (hts.trans hsg'.symm)

/-- The set of parameters where two continuations agree is closed. -/
theorem isClosed_setOf_eventuallyEq (hf : IsContinuationAlong γ f r)
    (hg : IsContinuationAlong γ g ρ) : IsClosed {t : I | f t =ᶠ[𝓝 (γ t)] g t} := by
  rw [← closure_subset_iff_isClosed]
  intro t ht
  rw [mem_closure_iff_nhds] at ht
  obtain ⟨s, ⟨⟨hsf, hsf'⟩, ⟨hsg, hsg'⟩⟩, hs⟩ := ht _ (inter_mem (hf.compat t) (hg.compat t))
  have hs' : γ s ∈ ball (γ t) (min (r t) (ρ t)) := by
    rw [mem_ball, lt_min_iff]
    exact ⟨hsf, hsg⟩
  have hst : f t =ᶠ[𝓝 (γ s)] g t := hsf'.symm.trans (hs.trans hsg')
  exact hf.eventuallyEq_center_of_eventuallyEq hg t hs' hst

/-- **Uniqueness of analytic continuation.** Two continuations along the same path whose germs
agree at the initial point have germs that agree at every parameter. -/
theorem eventuallyEq_of_eventuallyEq (hf : IsContinuationAlong γ f r)
    (hg : IsContinuationAlong γ g ρ) (h0 : f 0 =ᶠ[𝓝 (γ 0)] g 0) (t : I) :
    f t =ᶠ[𝓝 (γ t)] g t := by
  have hclopen : IsClopen {t : I | f t =ᶠ[𝓝 (γ t)] g t} :=
    ⟨hf.isClosed_setOf_eventuallyEq hg, hf.isOpen_setOf_eventuallyEq hg⟩
  have huniv := hclopen.eq_univ ⟨0, h0⟩
  have : t ∈ {t : I | f t =ᶠ[𝓝 (γ t)] g t} := by
    rw [huniv]
    exact mem_univ t
  exact this

/-- **Uniqueness of analytic continuation** at the end point of the path. -/
theorem eventuallyEq_one_of_eventuallyEq_zero (hf : IsContinuationAlong γ f r)
    (hg : IsContinuationAlong γ g ρ) (h0 : f 0 =ᶠ[𝓝 (γ 0)] g 0) :
    f 1 =ᶠ[𝓝 (γ 1)] g 1 :=
  hf.eventuallyEq_of_eventuallyEq hg h0 1

end IsContinuationAlong

/-- A function analytic on an open set containing the path is its own continuation along the
path, with any positive radii keeping the discs inside the set. -/
theorem isContinuationAlong_of_analyticOnNhd {U : Set ℂ} (hU : IsOpen U) {γ : I → ℂ}
    (hγ : Continuous γ) (hγU : ∀ t, γ t ∈ U) {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) :
    ∃ r : I → ℝ, IsContinuationAlong γ (fun _ => F) r := by
  have hr : ∀ t, ∃ r > 0, ball (γ t) r ⊆ U := fun t => Metric.isOpen_iff.mp hU _ (hγU t)
  choose r hr hrU using hr
  refine ⟨r, hr, fun t => hF.mono (hrU t), fun t => ?_⟩
  have : ∀ᶠ s in 𝓝 t, γ s ∈ ball (γ t) (r t) :=
    hγ.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self (hr t)))
  filter_upwards [this] with s hs
  exact ⟨hs, EventuallyEq.rfl⟩

end Complex

end
