/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Holomorphic.LocallyUniformLimit

/-!
# One-variable holomorphic function spaces

Mathlib's one-variable Weierstrass theorem makes the shared compact-open space of
holomorphic maps closed and complete. This module re-exports those results from
`ToMathlib.Analysis.Holomorphic.LocallyUniformLimit` and has no SCV dependency.

## Main results

* `Complex.isClosed_holomorphicSubmodule`: Locally uniform limits make the space of holomorphic
  maps on a planar open set closed.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/
