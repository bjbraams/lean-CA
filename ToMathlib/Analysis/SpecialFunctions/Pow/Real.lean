/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Natural powers of inverses as real powers

A natural power of the inverse of a nonnegative real number is the real power with the negated
exponent. This identity converts summability statements for `‖a i‖⁻¹ ^ n` into statements for
`‖a i‖ ^ (-s)` with real `s`.

## Main results

* `Real.inv_pow_eq_rpow_neg`: `x⁻¹ ^ n = x ^ (-(n : ℝ))` for `0 ≤ x`.
-/

public section

namespace Real

/-- For a nonnegative real base, a natural power of its inverse is the real power with the
corresponding negative exponent. -/
theorem inv_pow_eq_rpow_neg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : x⁻¹ ^ n = x ^ (-(n : ℝ)) := by
  rw [rpow_neg hx, rpow_natCast, inv_pow]

end Real
