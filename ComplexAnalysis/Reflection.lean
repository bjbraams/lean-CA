/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import TauCeti.Analysis.Complex.Conformal.Reflection.Principle

/-!
# Schwarz reflection across the real axis

A function holomorphic above the real axis, continuous up to the axis, and real-valued
on it extends holomorphically to a conjugation-invariant open domain. Below the axis the
extension is `conj (f (conj z))`. Continuity and analyticity use the imported proofs of the
Tau Ceti contributors in `TauCeti.Analysis.Complex.Conformal.Reflection.Principle`, adapted
to the existing local definition of the extension.

## Main results

* `Complex.schwarzReflection_of_nonneg`: The reflection preserves all values on and above the
  real axis.
* `Complex.schwarzReflection_of_neg`: Below the axis the reflected value is the conjugate of the
  value at the reflected point.
* `Complex.continuousOn_schwarzReflection`: Schwarz reflection is continuous when the
  upper-half-domain function is continuous up to the axis and takes real values on the axis.
* `Complex.analyticOnNhd_schwarzReflection`: **Schwarz reflection principle.** Real continuous
  boundary values allow holomorphic extension from the upper half of a conjugation-invariant
  open domain to the whole domain.
* `Complex.eqOn_schwarzReflection_of_analyticOnNhd`: A holomorphic extension agreeing above the
  axis agrees with the Schwarz extension throughout a connected domain, provided the upper half
  is nonempty.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Filter Function
open scoped Topology ComplexConjugate

namespace Complex

/-- Extend the upper-half-plane values by Schwarz reflection across the real axis. -/
@[expose] def schwarzReflection (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then f z else conj (f (conj z))

/-- The reflection preserves all values on and above the real axis. -/
@[simp] theorem schwarzReflection_of_nonneg {f : ℂ → ℂ} {z : ℂ} (hz : 0 ≤ z.im) :
    schwarzReflection f z = f z := ite_eq_left hz

/-- Below the axis the reflected value is the conjugate of the value at the reflected point. -/
theorem schwarzReflection_of_neg {f : ℂ → ℂ} {z : ℂ} (hz : z.im < 0) :
    schwarzReflection f z = conj (f (conj z)) := ite_eq_right (not_le_of_gt hz)

/-- Schwarz reflection is continuous when the upper-half-domain function is continuous
up to the axis and takes real values on the axis.

Uses `TauCeti.continuousOn_schwarzReflection_of_symmetric`. -/
theorem continuousOn_schwarzReflection {U : Set ℂ} {f : ℂ → ℂ}
    (hs : MapsTo conj U U) (hc : ContinuousOn f (U ∩ {z | 0 ≤ z.im}))
    (hr : ∀ z ∈ U, z.im = 0 → (f z).im = 0) : ContinuousOn (schwarzReflection f) U := by
  have heq : TauCeti.schwarzReflection f = schwarzReflection f := by
    funext z
    exact TauCeti.schwarzReflection_def f z
  rw [← heq]
  exact TauCeti.continuousOn_schwarzReflection_of_symmetric hs hc hr

/-- **Schwarz reflection principle.** Real continuous boundary values allow holomorphic
extension from the upper half of a conjugation-invariant open domain to the whole domain.

Uses `TauCeti.differentiableOn_schwarzReflection_of_symmetric`. -/
theorem analyticOnNhd_schwarzReflection {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hs : MapsTo conj U U)
    (hc : ContinuousOn f (U ∩ {z | 0 ≤ z.im}))
    (hd : DifferentiableOn ℂ f (U ∩ {z | 0 < z.im}))
    (hr : ∀ z ∈ U, z.im = 0 → (f z).im = 0) :
    AnalyticOnNhd ℂ (schwarzReflection f) U := by
  have heq : TauCeti.schwarzReflection f = schwarzReflection f := by
    funext z
    exact TauCeti.schwarzReflection_def f z
  rw [← heq]
  exact (TauCeti.differentiableOn_schwarzReflection_of_symmetric hU hs hc hd hr).analyticOnNhd hU

/-- A holomorphic extension agreeing above the axis agrees with the Schwarz extension
throughout a connected domain, provided the upper half is nonempty. -/
theorem eqOn_schwarzReflection_of_analyticOnNhd {U : Set ℂ} {f g : ℂ → ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hs : MapsTo conj U U)
    (hc : ContinuousOn f (U ∩ {z | 0 ≤ z.im}))
    (hd : DifferentiableOn ℂ f (U ∩ {z | 0 < z.im}))
    (hr : ∀ z ∈ U, z.im = 0 → (f z).im = 0)
    (hne : (U ∩ {z | 0 < z.im}).Nonempty) (hg : AnalyticOnNhd ℂ g U)
    (he : EqOn g f (U ∩ {z | 0 < z.im})) : EqOn g (schwarzReflection f) U := by
  obtain ⟨a, ha⟩ := hne
  apply hg.eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_schwarzReflection hU hs hc hd hr) hconn ha.1
  filter_upwards [(hU.inter (isOpen_lt continuous_const continuous_im)).mem_nhds ha] with z hz
  rw [schwarzReflection_of_nonneg hz.2.le]
  exact he hz

end Complex
