/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.BranchLog.Analytic
public import Mathlib.Topology.Homotopy.Path
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Logarithm branches along homotopies

A homotopy of paths in the punctured plane has a continuous logarithm on its
parameter square, uniquely normalized at the initial endpoint. Its values on
both endpoint edges are constant. Consequently, continuation of a logarithm
along homotopic paths gives the same terminal value.

These statements require only continuity of the homotopy, not differentiability
or existence of a logarithm on an ambient planar domain.

## Main results

* `Complex.exists_logBranch_homotopy`: A path homotopy avoiding zero has a continuous logarithm,
  prescribed on the initial edge and constant on the terminal edge.
* `Complex.logBranch_endpoint_eq_of_homotopy`: Logarithms continued along homotopic paths
  avoiding zero have the same terminal value if they have the same initial value. The homotopy
  need only be continuous.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public section
open Set
open scoped unitInterval
namespace Complex

/-- A path homotopy avoiding zero has a continuous logarithm, prescribed on the initial
edge and constant on the terminal edge. -/
theorem exists_logBranch_homotopy {a b l : ℂ} {γ δ : Path a b} (H : γ.Homotopy δ)
    (hH : ∀ p, H p ≠ 0) (hl : exp l = a) :
    ∃ L : C(I × I, ℂ), (∀ p, exp (L p) = H p) ∧
      (∀ s, L (s, 0) = l) ∧ ∀ s, L (s, 1) = L (0, 1) := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨L, ⟨hL0, he⟩, _⟩ := isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (⟨H, H.continuous⟩ : C(I × I, ℂ)) (a₀ := (0, 0)) (by simpa using hl) hH
  have hL (p : I × I) : exp (L p) = H p := congrFun he p
  refine ⟨L, hL, ?_, ?_⟩
  · intro s
    exact eqOn_logBranch_of_continuousOn isPreconnected_univ
      (L.continuous.comp (show Continuous (fun s : I => (s, (0 : I))) by fun_prop)).continuousOn
      continuousOn_const
      (g := fun _ : I => a) (by intro t _; simpa using hL (t, 0))
      (by intro _ _; exact hl) (mem_univ 0) hL0 (mem_univ s)
  · intro s
    exact eqOn_logBranch_of_continuousOn isPreconnected_univ
      (L.continuous.comp (show Continuous (fun s : I => (s, (1 : I))) by fun_prop)).continuousOn
      continuousOn_const
      (g := fun _ : I => b) (by intro t _; simpa using hL (t, 1))
      (by intro _ _; simpa using hL (0, 1)) (mem_univ 0) rfl (mem_univ s)

/-- Logarithms continued along homotopic paths avoiding zero have the same terminal value
if they have the same initial value. The homotopy need only be continuous. -/
theorem logBranch_endpoint_eq_of_homotopy {a b : ℂ} {γ δ : Path a b}
    (H : γ.Homotopy δ) (hH : ∀ p, H p ≠ 0) {L M : I → ℂ}
    (hL : Continuous L) (hM : Continuous M)
    (heL : ∀ t, exp (L t) = γ t) (heM : ∀ t, exp (M t) = δ t)
    (hzero : L 0 = M 0) : L 1 = M 1 := by
  obtain ⟨N, heN, hN0, hN1⟩ := exists_logBranch_homotopy H hH
    (by simpa using heL 0)
  have hleft : ∀ t, N (0, t) = L t := fun t =>
    eqOn_logBranch_of_continuousOn isPreconnected_univ
      (N.continuous.comp (show Continuous (fun s : I => ((0 : I), s)) by fun_prop)).continuousOn
      hL.continuousOn
      (g := γ) (by intro s _; simpa using heN (0, s))
      (by intro s _; exact heL s) (mem_univ 0) (hN0 0) (mem_univ t)
  have hright : ∀ t, N (1, t) = M t := fun t =>
    eqOn_logBranch_of_continuousOn isPreconnected_univ
      (N.continuous.comp (show Continuous (fun s : I => ((1 : I), s)) by fun_prop)).continuousOn
      hM.continuousOn
      (g := δ) (by intro s _; simpa using heN (1, s))
      (by intro s _; exact heM s) (mem_univ 0) ((hN0 1).trans hzero) (mem_univ t)
  exact (hleft 1).symm.trans ((hN1 1).symm.trans (hright 1))

end Complex
