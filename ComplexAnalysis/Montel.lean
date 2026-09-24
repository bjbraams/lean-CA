/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Analysis.Holomorphic.NormalFamily
public import ComplexAnalysis.FunctionSpace

/-!
# Montel's theorem in one variable

A compact-locally bounded family of holomorphic maps with finite-dimensional target has
compact closure. Every such sequence has a locally uniformly convergent subsequence with
holomorphic limit. All compactness arguments are shared with SCV through `Analysis`.

## Main results

* `Complex.isCompact_closure_of_holomorphic_bounded_on_compacts`: **Montel's theorem** in the
  compact-open holomorphic function space.
* `Complex.exists_subseq_tendstoLocallyUniformlyOn_of_bounded_on_compacts`: A compact-locally
  bounded sequence of holomorphic functions has a locally uniformly convergent subsequence with
  holomorphic limit.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Filter Function Set
open scoped Topology

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F] [FiniteDimensional ℂ F]

/-- **Montel's theorem** in the compact-open holomorphic function space.

A scalar version is formalized in Vincent Beffara's RMT4. See `CREDITS.md`. -/
theorem isCompact_closure_of_holomorphic_bounded_on_compacts
    {U : TopologicalSpace.Opens ℂ} {S : Set (HolomorphicMap U F)}
    (hb : ∀ K ⊆ (U : Set ℂ), IsCompact K → ∃ M : ℝ,
      ∀ f ∈ S, ∀ z ∈ K, ‖openExtension U f.val z‖ ≤ M) : IsCompact (closure S) :=
  isCompact_closure_of_holomorphic_bounded_on_compacts_of_isClosed
    (isClosed_holomorphicSubmodule U) hb

/-- A compact-locally bounded sequence of holomorphic functions has a locally uniformly
convergent subsequence with holomorphic limit.

Scalar counterparts appear in Vincent Beffara's RMT4 and the `phasetr/ising-model` project. See
`CREDITS.md`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_bounded_on_compacts
    {U : Set ℂ} (hU : IsOpen U) {f : ℕ → ℂ → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∃ (g : ℂ → F) (φ : ℕ → ℕ), StrictMono φ ∧ DifferentiableOn ℂ g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U := by
  let V : TopologicalSpace.Opens ℂ := ⟨U, hU⟩
  let s (n : ℕ) := holomorphicMapOfAnalyticOnNhd V (f n) ((hf n).analyticOnNhd hU)
  obtain ⟨g, φ, hφ, hlim⟩ :=
    exists_subseq_tendsto_of_holomorphic_bounded_on_compacts_of_isClosed
      (isClosed_holomorphicSubmodule V) s (by
        intro K hKU hK
        obtain ⟨M, hM⟩ := hb K hKU hK
        refine ⟨M, fun n z hz => ?_⟩
        rw [openExtension_apply V _ (hKU hz)]
        exact hM n z hz)
  refine ⟨openExtension V g.val, φ, hφ, g.property.differentiableOn, ?_⟩
  exact (holomorphicMap_tendsto_iff.mp hlim).congr (fun n z hz => by
    rw [openExtension_apply V _ hz]; rfl)

end Complex
