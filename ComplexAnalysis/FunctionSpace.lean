/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Holomorphic.FunctionSpace
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# One-variable holomorphic function spaces

Mathlib's one-variable Weierstrass theorem makes the shared compact-open space of
holomorphic maps closed and complete. This module has no SCV dependency.

## Main results

* `Complex.isClosed_holomorphicSubmodule`: Locally uniform limits make the space of holomorphic
  maps on a planar open set closed.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public section

open Filter Set
open scoped Topology

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Locally uniform limits make the space of holomorphic maps on a planar open set closed. -/
theorem isClosed_holomorphicSubmodule (U : TopologicalSpace.Opens ℂ) :
    IsClosed (holomorphicSubmodule (F := F) U : Set C(U, F)) := by
  rw [isClosed_iff_forall_filter]
  intro f l hl hmem hlim
  have hc : Tendsto (fun g : C(U, F) ↦ g) l (𝓝 f) := hlim
  have ha : ∀ᶠ g in l, AnalyticOnNhd ℂ (openExtension U g) U := le_principal_iff.mp hmem
  exact ((tendsto_iff_openExtension.mp hc).differentiableOn
    (ha.mono fun _ h ↦ h.differentiableOn) U.isOpen).analyticOnNhd U.isOpen

/-- Holomorphic maps from a planar open set to a Banach space form a complete uniform space. -/
instance (U : TopologicalSpace.Opens ℂ) : CompleteSpace (HolomorphicMap U F) :=
  (isClosed_holomorphicSubmodule (F := F) U).isComplete.completeSpace_coe

end Complex
