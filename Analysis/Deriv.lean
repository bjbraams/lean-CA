/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Differentiation along the diagonal

The diagonal chain rule for a differentiable function on a product, with values in
a normed space over a nontrivially normed field.

## Main results

* `deriv_diagonal`: The derivative along the diagonal is the sum of the two coordinate
  derivatives.

## References

* `Mathlib.Analysis.Calculus.Deriv.Prod`: formal background used by this module.
* `Mathlib.Analysis.Calculus.Deriv.Comp`: formal background used by this module.
-/

public noncomputable section

/-- The derivative along the diagonal is the sum of the two coordinate derivatives. -/
theorem deriv_diagonal {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : 𝕜 × 𝕜 → E} {t : 𝕜}
    (hF : DifferentiableAt 𝕜 F (t, t)) :
    deriv (fun s => F (s, s)) t =
      deriv (fun s => F (s, t)) t + deriv (fun s => F (t, s)) t := by
  have h₁ := hF.hasFDerivAt.comp_hasDerivAt_of_eq t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t t)) rfl
  have h₂ := hF.hasFDerivAt.comp_hasDerivAt_of_eq t
    ((hasDerivAt_const t t).prodMk (hasDerivAt_id t)) rfl
  have h := hF.hasFDerivAt.comp_hasDerivAt_of_eq t
    ((hasDerivAt_id t).prodMk (hasDerivAt_id t)) rfl
  simp only [Function.comp_def, id_eq] at h h₁ h₂
  rw [h.deriv, h₁.deriv, h₂.deriv, ← map_add]
  simp

end
