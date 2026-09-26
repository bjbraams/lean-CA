/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Simple connectedness of convex sets

A nonempty convex subset of a real topological vector space is contractible, hence simply
connected.

## Main results

* `Convex.isSimplyConnected`: nonempty convex sets are simply connected.
-/

public section

/-- A nonempty convex set in a real topological vector space is simply connected. -/
theorem Convex.isSimplyConnected {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {s : Set E} (hs : Convex ℝ s)
    (hne : s.Nonempty) : IsSimplyConnected s :=
  have : ContractibleSpace s := hs.contractibleSpace hne
  (inferInstance : SimplyConnectedSpace s)

end
