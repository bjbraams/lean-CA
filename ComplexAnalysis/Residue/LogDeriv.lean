/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Residue
public import Mathlib.Analysis.Meromorphic.LogDeriv

/-!
# Residues of logarithmic derivatives

For a nonzero meromorphic germ the residue of its logarithmic derivative is its
integer order: positive at a zero and negative at a pole. The proof uses Mathlib's
local meromorphic factorization, so no choice of a Laurent expansion is required.

## Main results

* `AnalyticAt.logDeriv`: The logarithmic derivative of a nonvanishing analytic germ is analytic.
* `Complex.residue_logDeriv_of_order`: The residue of a logarithmic derivative equals the
  integer order of the meromorphic germ.
* `Complex.residue_logDeriv`: The residue of the logarithmic derivative of a nonzero meromorphic
  germ is its order.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace Complex

/-- The logarithmic derivative of a nonvanishing analytic germ is analytic. -/
theorem _root_.AnalyticAt.logDeriv {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hne : f c ≠ 0) : AnalyticAt ℂ (logDeriv f) c :=
  hf.deriv.div hf hne

/-- The residue of a logarithmic derivative equals the integer order of the meromorphic germ. -/
theorem residue_logDeriv_of_order {f : ℂ → ℂ} {c : ℂ} {n : ℤ}
    (hf : MeromorphicAt f c) (hn : meromorphicOrderAt f c = n) :
    residue (logDeriv f) c = (n : ℂ) := by
  obtain ⟨g, hg, hgc, he⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn
  have hlog : logDeriv f =ᶠ[𝓝[≠] c]
      (fun z => (n : ℂ) / (z - c) + logDeriv g z) := by
    apply (logDeriv_congr_nhdsNE he).trans
    filter_upwards [hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (hg.continuousAt.eventually_ne hgc).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hgz hzc
    have hne : z - c ≠ 0 := sub_ne_zero.mpr hzc
    change logDeriv (fun z => (z - c) ^ n * g z) z = _
    rw [logDeriv_fun_mul (f := fun w : ℂ => (w - c) ^ n) (g := g) z
      (zpow_ne_zero n hne) hgz
      ((differentiableAt_id.sub_const c).zpow (Or.inl hne)) hz.differentiableAt,
      logDeriv_fun_zpow (f := fun w : ℂ => w - c) (by fun_prop) n]
    simp [logDeriv_apply, div_eq_mul_inv]
  rw [residue_congr hlog]
  have hk : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ (fun z => (n : ℂ) / (z - c)) z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz)
  rw [residue_add hk ((hg.logDeriv hgc).eventually_analyticAt.filter_mono nhdsWithin_le_nhds),
    residue_div_sub analyticAt_const, (hg.logDeriv hgc).residue_eq_zero, add_zero]

/-- The residue of the logarithmic derivative of a nonzero meromorphic germ is its order. -/
theorem residue_logDeriv {f : ℂ → ℂ} {c : ℂ}
    (hf : MeromorphicAt f c) (hne : meromorphicOrderAt f c ≠ ⊤) :
    residue (logDeriv f) c = ((meromorphicOrderAt f c).untop₀ : ℂ) :=
  residue_logDeriv_of_order hf (WithTop.coe_untop₀_of_ne_top hne).symm

end Complex
