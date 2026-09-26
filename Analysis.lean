/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Analysis.Holomorphic.FunctionSpace
public import Analysis.Holomorphic.NormalFamily
public import Analysis.Integral.CompactSupport
public import Analysis.Integral.CurveIntegral
public import Analysis.Integral.CurveIntegral.Map
public import Analysis.Integral.CurveIntegral.Improper
public import Analysis.TaylorBounds

/-!
# General analysis support

Spaces of holomorphic maps with the compact-open topology and the shared Montel and Vitali
arguments, integration of compactly supported and weighted functions, curve integration of
exact one-forms (pullback along mapped paths and improper endpoint formulas), and elementary
real Taylor-remainder bounds. Declarations use the namespaces of their underlying Mathlib
APIs. This library depends only on Mathlib.

## Main results

This module re-exports the following developments:

* `Analysis.Holomorphic.FunctionSpace`: Shared spaces of holomorphic maps.
* `Analysis.Holomorphic.NormalFamily`: Shared Montel and Vitali arguments.
* `Analysis.Integral.CompactSupport`: Integration helpers for compactly supported and weighted
  functions.
* `Analysis.Integral.CurveIntegral`: Integrating exact one-forms along curves.
* `Analysis.Integral.CurveIntegral.Map`: Pullback of one-forms along mapped paths.
* `Analysis.Integral.CurveIntegral.Improper`: Endpoint formulas for improper integrals of exact
  one-forms.
* `Analysis.TaylorBounds`: Elementary bounds for Taylor remainders.
-/
