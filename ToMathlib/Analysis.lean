/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Holomorphic.FunctionSpace
public import ToMathlib.Analysis.Holomorphic.NormalFamily
public import ToMathlib.Analysis.Integral.CompactSupport
public import ToMathlib.Analysis.Integral.CurveIntegral
public import ToMathlib.Analysis.Integral.CurveIntegral.Map
public import ToMathlib.Analysis.Integral.CurveIntegral.Improper
public import ToMathlib.Analysis.Integral.CurveIntegral.SmoothConcat
public import ToMathlib.Analysis.TaylorBounds

/-!
# General analysis support

Spaces of holomorphic maps with the compact-open topology and the shared Montel and Vitali
arguments, integration of compactly supported and weighted functions, curve integration of
exact one-forms (pullback along mapped paths, improper endpoint formulas, and smooth
concatenation of paths), and elementary
real Taylor-remainder bounds. Declarations use the namespaces of their underlying Mathlib
APIs. This library depends only on Mathlib.

## Main results

This module re-exports the following developments:

* `ToMathlib.Analysis.Holomorphic.FunctionSpace`: Shared spaces of holomorphic maps.
* `ToMathlib.Analysis.Holomorphic.NormalFamily`: Shared Montel and Vitali arguments.
* `ToMathlib.Analysis.Integral.CompactSupport`: Integration helpers for compactly supported
  and weighted functions.
* `ToMathlib.Analysis.Integral.CurveIntegral`: Integrating exact one-forms along curves.
* `ToMathlib.Analysis.Integral.CurveIntegral.Map`: Pullback of one-forms along mapped paths.
* `ToMathlib.Analysis.Integral.CurveIntegral.Improper`: Endpoint formulas for improper
  integrals of exact one-forms.
* `ToMathlib.Analysis.Integral.CurveIntegral.SmoothConcat`: Smooth concatenation of chains of
  paths, with additivity of curve integrals.
* `ToMathlib.Analysis.TaylorBounds`: Elementary bounds for Taylor remainders.
-/
