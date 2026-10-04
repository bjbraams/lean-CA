/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Holomorphic.NormalFamily
public import ComplexAnalysis.FunctionSpace
public import TauCeti.Analysis.Complex.Conformal.Montel.Basic

/-!
# Montel's theorem in one variable

A compact-locally bounded family of holomorphic maps with finite-dimensional target has
compact closure. Every such sequence has a locally uniformly convergent subsequence with
holomorphic limit. The bundled compactness results are shared with SCV through `Analysis`.
The ambient-function subsequence theorem adapts the Tau Ceti contributors' `TauCeti.montel`
from `TauCeti.Analysis.Complex.Conformal.Montel.Basic`, retaining finite-dimensional targets.

## Main results

* `Complex.isCompact_closure_of_holomorphic_bounded_on_compacts`: the shared Montel
  theorem, with bounds directly on compact subsets of the domain.
* `Complex.isCompact_closure_of_holomorphic_bounded_on_compacts_of_openExtension`: the
  variant using bounds for the ambient extension by zero.
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

/-- **Montel's theorem** with compact-local bounds on the ambient extension by zero.

A scalar version is formalized in Vincent Beffara's RMT4. See `CREDITS.md`. -/
theorem isCompact_closure_of_holomorphic_bounded_on_compacts_of_openExtension
    {U : TopologicalSpace.Opens ℂ} {S : Set (HolomorphicMap U F)}
    (hb : ∀ K ⊆ (U : Set ℂ), IsCompact K → ∃ M : ℝ,
      ∀ f ∈ S, ∀ z ∈ K, ‖openExtension U f.val z‖ ≤ M) : IsCompact (closure S) :=
  isCompact_closure_of_holomorphic_bounded_on_compacts_of_isClosed
    (isClosed_holomorphicSubmodule U) hb

-- Retain the existing completeness parameter in the public interface.
set_option linter.unusedSectionVars false in
/-- A compact-locally bounded sequence of holomorphic functions has a locally uniformly
convergent subsequence with holomorphic limit.

This adapts the Tau Ceti contributors' `TauCeti.montel` from
`TauCeti.Analysis.Complex.Conformal.Montel.Basic`; the compactness proof is imported.

Scalar counterparts appear in Vincent Beffara's RMT4 and the `phasetr/ising-model` project. See
`CREDITS.md`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_bounded_on_compacts
    {U : Set ℂ} (hU : IsOpen U) {f : ℕ → ℂ → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∃ (g : ℂ → F) (φ : ℕ → ℕ), StrictMono φ ∧ DifferentiableOn ℂ g U ∧
      TendstoLocallyUniformlyOn (fun n ↦ f (φ n)) g atTop U := by
  obtain ⟨φ, g, hφ, hg, hlim⟩ :=
    TauCeti.montel hU hf (TauCeti.isLocallyBoundedOn_def.mpr hb)
  exact ⟨g, φ, hφ, hg, hlim⟩

end Complex
