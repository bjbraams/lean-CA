/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Topology.LocallyConstantGluing
public import Topology.Frontier
public import Topology.SimplyConnected
public import Topology.UpperSemicontinuous

/-!
# General topology support

Gluing functions with locally constant differences on simply connected spaces, frontier and
complementary-component lemmas, simple connectedness of convex sets, and semicontinuity. Declarations extend the existing Mathlib
APIs. This library has no dependency on project analysis or complex function theory.

## Main results

This module re-exports the following developments:

* `Topology.LocallyConstantGluing`: Gluing functions with locally constant differences.
* `Topology.Frontier`: Frontiers and complementary components.
* `Topology.SimplyConnected`: Simple connectedness of convex sets.
* `Topology.UpperSemicontinuous`: Nonnegative multiples of upper semicontinuous functions.
-/
