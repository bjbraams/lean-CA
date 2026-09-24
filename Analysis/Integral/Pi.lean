/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Nonnegative integration on finite product spaces

Finite-product versions of Tonelli's theorem for products of measurable coordinate
functions. The coordinate spaces may differ and the index type may be empty.

## Main results

* `MeasureTheory.lintegral_fin_nat_prod_eq_prod`: A nonnegative product of coordinate functions
  integrates as the product of its integrals, for a dependent family indexed by `Fin n`,
  including the empty product.
* `MeasureTheory.lintegral_fintype_prod_eq_prod`: A nonnegative product of coordinate functions
  integrates as the product of its integrals on an arbitrary finite dependent product of
  sigma-finite measure spaces.

## References

* `Mathlib.MeasureTheory.Integral.Pi`: formal background used by this module.
-/

public noncomputable section
open scoped ENNReal
namespace MeasureTheory

set_option backward.isDefEq.respectTransparency false in
/-- A nonnegative product of coordinate functions integrates as the product of its integrals,
for a dependent family indexed by `Fin n`, including the empty product. -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (measurePreserving_piFinSuccAbove μ 0).symm.lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    have hg : Measurable (fun x : (i : Fin n) → E i.succ => ∏ i, f i.succ (x i)) := by fun_prop
    have : SFinite (Measure.pi fun j : Fin n => μ j.succ) := inferInstance
    rw [lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable,
      ih _ (fun i => hf i.succ)]

/-- A nonnegative product of coordinate functions integrates as the product of its integrals
on an arbitrary finite dependent product of sigma-finite measure spaces. -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod _ (fun i => hf (e i))

end MeasureTheory
end
