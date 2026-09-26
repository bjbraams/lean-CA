/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.BranchLog
import Mathlib.Analysis.Complex.CoveringMap

/-!
# Analytic dependence of logarithm branches

A continuous logarithm branch of an analytic complex-valued function is analytic,
also when its source is a complex normed space. This upgrades Mathlib's covering-space
construction to analytic logarithms with auxiliary complex parameters.

## Main results

* `Complex.eqOn_logBranch_of_continuousOn`: Continuous logarithm branches on a preconnected set
  agree if they agree at one point. No differentiability or complex structure on the source
  space is required.
* `Complex.analyticAt_logBranch`: A continuous logarithm of an analytic function is analytic
  near the base point.
* `Complex.analyticOnNhd_logBranch`: Continuous logarithm branches preserve analytic dependence
  on any complex normed source.
* `Complex.exists_analyticOnNhd_logBranch_of_analyticOnNhd`: A nonvanishing analytic function on
  a simply connected open set has an analytic logarithm, including for normed source spaces with
  auxiliary complex parameters.
* `Complex.exists_analyticOnNhd_logBranch_zero_section`: A family equal to one on the zero
  section admits a logarithm vanishing there. The domain must contain the zero section over each
  of its fibers.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public section
open Set Filter
open scoped Topology
namespace Complex

/-- Continuous logarithm branches on a preconnected set agree if they agree at one point.
No differentiability or complex structure on the source space is required. -/
theorem eqOn_logBranch_of_continuousOn
    {X : Type*} [TopologicalSpace X] {U : Set X} (hUc : IsPreconnected U)
    {g L M : X → ℂ} (hL : ContinuousOn L U) (hM : ContinuousOn M U)
    (heL : EqOn (exp ∘ L) g U) (heM : EqOn (exp ∘ M) g U)
    {x : X} (hx : x ∈ U) (he : L x = M x) : EqOn L M U := by
  apply isCoveringMap_exp.eqOn_of_comp_eqOn hUc hL hM ?_ hx he
  intro y hy
  exact Subtype.ext ((heL hy).trans (heM hy).symm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous logarithm of an analytic function is analytic near the base point. -/
theorem analyticAt_logBranch {g L : E → ℂ} {x : E}
    (hg : AnalyticAt ℂ g x) (hL : ContinuousAt L x)
    (heq : exp ∘ L =ᶠ[𝓝 x] g) : AnalyticAt ℂ L x := by
  have hx : exp (L x) = g x := heq.self_of_nhds
  have hg0 : g x ≠ 0 := hx ▸ exp_ne_zero (L x)
  have ha : AnalyticAt ℂ (fun y ↦ L x + log (g y / g x)) x :=
    analyticAt_const.add ((hg.div_const (c := g x)).clog (by simp [hg0]))
  apply ha.congr
  have hband : ∀ᶠ y in 𝓝 x, (L y - L x).im ∈ Ioo (-Real.pi) Real.pi := by
    apply ((continuous_im.continuousAt.comp (hL.sub_const (L x))).tendsto).eventually
    apply Ioo_mem_nhds <;> simpa using Real.pi_pos
  filter_upwards [heq, hband] with y hy hby
  rw [← hx, ← hy, Function.comp_apply, ← exp_sub, log_exp hby.1 hby.2.le]
  ring

/-- Continuous logarithm branches preserve analytic dependence on any complex normed source. -/
theorem analyticOnNhd_logBranch {U : Set E} (hU : IsOpen U) {g L : E → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hL : ContinuousOn L U)
    (heq : EqOn (exp ∘ L) g U) : AnalyticOnNhd ℂ L U := by
  intro x hx
  exact analyticAt_logBranch (hg x hx) (hL.continuousAt (hU.mem_nhds hx))
    (heq.eventuallyEq_of_mem (hU.mem_nhds hx))

/-- A nonvanishing analytic function on a simply connected open set has an analytic logarithm,
including for normed source spaces with auxiliary complex parameters.

For a one-variable disk-domain counterpart, see Geoffrey Irving's `ray` formalization. See
`CREDITS.md`. -/
theorem exists_analyticOnNhd_logBranch_of_analyticOnNhd
    {U : Set E} (hU : IsOpen U) (hUc : IsSimplyConnected U) {g : E → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ x ∈ U, g x ≠ 0) :
    ∃ L : E → ℂ, AnalyticOnNhd ℂ L U ∧ EqOn (exp ∘ L) g U := by
  obtain ⟨L, hL, heq⟩ := exists_continuousOn_eqOn_exp_comp hUc hU hg.continuousOn
    (by rintro ⟨x, hx, heq⟩; exact hg0 x hx heq)
  exact ⟨L, analyticOnNhd_logBranch hU hg hL heq, heq⟩

/-- A family equal to one on the zero section admits a logarithm vanishing there.
The domain must contain the zero section over each of its fibers. -/
theorem exists_analyticOnNhd_logBranch_zero_section
    {W : Set (E × ℂ)} (hW : IsOpen W) (hWc : IsSimplyConnected W)
    (hsection : ∀ p ∈ W, (p.1, (0 : ℂ)) ∈ W) {g : E × ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g W) (hg0 : ∀ p ∈ W, g p ≠ 0)
    (hzero : ∀ p : E, (p, (0 : ℂ)) ∈ W → g (p, 0) = 1) :
    ∃ L : E × ℂ → ℂ, AnalyticOnNhd ℂ L W ∧ EqOn (exp ∘ L) g W ∧
      ∀ p : E, L (p, 0) = 0 := by
  obtain ⟨L, hL, he⟩ := exists_analyticOnNhd_logBranch_of_analyticOnNhd hW hWc hg hg0
  change ∀ p ∈ W, exp (L p) = g p at he
  refine ⟨fun p ↦ L p - L (p.1, 0), ?_, ?_, fun _ ↦ sub_self _⟩
  · apply hL.sub
    intro p hp
    exact (hL _ (hsection p hp)).comp_of_eq
      (analyticAt_fst.prod analyticAt_const) rfl
  · intro p hp
    change exp (L p - L (p.1, 0)) = g p
    rw [exp_sub, he p hp, he _ (hsection p hp), hzero p.1 (hsection p hp), div_one]

end Complex
