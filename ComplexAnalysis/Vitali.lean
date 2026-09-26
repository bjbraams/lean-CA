/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Montel
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Vitali's theorem in one variable

A compact-locally bounded holomorphic sequence which converges pointwise on a subset with
an accumulation point inside its connected open domain converges locally uniformly on the
whole domain. The shared Vitali argument uses the one-variable identity theorem to verify
that this subset is a uniqueness set. No SCV module is imported.

## Main results

* `Complex.exists_tendsto_of_holomorphic_bounded_on_compacts`: **Vitali's theorem** in the
  compact-open function space. Pointwise convergence on a set with an interior accumulation
  point determines convergence on the whole domain.
* `Complex.exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto`: **Vitali's theorem.** A
  compact-locally bounded holomorphic sequence converging pointwise on a set with an
  accumulation point in the domain converges locally uniformly everywhere in that connected open
  domain, to a holomorphic limit.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Filter Set
open scoped Topology

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F] [FiniteDimensional ℂ F]

/-- **Vitali's theorem** in the compact-open function space. Pointwise convergence on a
set with an interior accumulation point determines convergence on the whole domain.

A scalar Vitali–Porter counterpart is formalized by the `phasetr/ising-model` contributors. See
`CREDITS.md`. -/
theorem exists_tendsto_of_holomorphic_bounded_on_compacts
    {U : TopologicalSpace.Opens ℂ} (hconn : IsPreconnected (U : Set ℂ))
    (f : ℕ → HolomorphicMap U F)
    (hb : ∀ K ⊆ (U : Set ℂ), IsCompact K → ∃ M : ℝ,
      ∀ n, ∀ z ∈ K, ‖openExtension U (f n).val z‖ ≤ M)
    {V : Set ℂ} (hVU : V ⊆ U) {a : ℂ} (ha : a ∈ U)
    (hacc : a ∈ closure (V \ {a}))
    (hp : ∀ z ∈ V, ∃ y : F,
      Tendsto (fun n ↦ openExtension U (f n).val z) atTop (𝓝 y)) :
    ∃ g : HolomorphicMap U F, Tendsto f atTop (𝓝 g) := by
  apply exists_tendsto_of_holomorphic_bounded_on_compacts_of_isClosed_of_unique
    (isClosed_holomorphicSubmodule U) f hb hVU _ hp
  intro p q he
  have heq := p.property.eqOn_of_preconnected_of_mem_closure q.property hconn ha
    (closure_mono (show V \ {a} ⊆
      {z | openExtension U p.val z = openExtension U q.val z} \ {a} from
        fun _ hz ↦ ⟨he hz.1, hz.2⟩) hacc)
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  simpa only [openExtension_coe] using heq z.property

/-- **Vitali's theorem.** A compact-locally bounded holomorphic sequence converging pointwise
on a set with an accumulation point in the domain converges locally uniformly everywhere
in that connected open domain, to a holomorphic limit.

A scalar Vitali–Porter counterpart is formalized by the `phasetr/ising-model` contributors. See
`CREDITS.md`. -/
theorem exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto
    {D V : Set ℂ} (hD : IsOpen D) (hconn : IsPreconnected D) {f : ℕ → ℂ → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) D)
    (hb : ∀ K ⊆ D, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hVD : V ⊆ D) {a : ℂ} (ha : a ∈ D) (hacc : a ∈ closure (V \ {a}))
    (hp : ∀ z ∈ V, ∃ y : F, Tendsto (fun n ↦ f n z) atTop (𝓝 y)) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g D ∧ TendstoLocallyUniformlyOn f g atTop D := by
  let U : TopologicalSpace.Opens ℂ := ⟨D, hD⟩
  let s (n : ℕ) := holomorphicMapOfAnalyticOnNhd U (f n) ((hf n).analyticOnNhd hD)
  have hs (n : ℕ) {z : ℂ} (hz : z ∈ D) : openExtension U (s n).val z = f n z :=
    openExtension_apply U _ hz
  obtain ⟨g, hg⟩ := exists_tendsto_of_holomorphic_bounded_on_compacts hconn s
    (by
      intro K hKD hK
      obtain ⟨M, hM⟩ := hb K hKD hK
      exact ⟨M, fun n z hz ↦ by rw [hs n (hKD hz)]; exact hM n z hz⟩)
    hVD ha hacc (by
      intro z hz
      simpa only [hs _ (hVD hz)] using hp z hz)
  exact ⟨openExtension U g.val, g.property.differentiableOn,
    (holomorphicMap_tendsto_iff.mp hg).congr (fun n _ hz ↦ hs n hz)⟩

end Complex
