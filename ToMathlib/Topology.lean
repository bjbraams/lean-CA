/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Topology.LocallyConstantGluing
public import ToMathlib.Topology.Frontier
public import ToMathlib.Topology.SimplyConnected
public import ToMathlib.Topology.UpperSemicontinuous

/-!
# General topology support

Gluing functions with locally constant differences on simply connected spaces, frontier and
complementary-component lemmas, simple connectedness of convex sets, and semicontinuity.
Declarations extend the existing Mathlib APIs. This library has no dependency on project
analysis or complex function theory.

## Main results

This module re-exports the following developments:

* `ToMathlib.Topology.LocallyConstantGluing`: Gluing functions with locally constant differences.
* `ToMathlib.Topology.Frontier`: Frontiers and complementary components.
* `ToMathlib.Topology.SimplyConnected`: Simple connectedness of convex sets.
* `ToMathlib.Topology.UpperSemicontinuous`: Nonnegative multiples of upper semicontinuous functions.
-/
