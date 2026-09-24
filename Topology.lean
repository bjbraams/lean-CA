/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Topology.LocallyConstantGluing
public import Topology.CompactExhaustion
public import Topology.Frontier
public import Topology.Graph
public import Topology.Path
public import Topology.SeparateContinuous
public import Topology.UpperSemicontinuous

/-!
# General topology support

Gluing functions with locally constant differences on simply connected spaces, compact
exhaustions, frontier and path lemmas, graph homeomorphisms, semicontinuity, and
Baire bounds for separately continuous maps. Declarations extend the existing Mathlib APIs.
This library has no dependency on project analysis, complex function theory, or applications.

## Main results

This module re-exports the following developments:

* `Topology.LocallyConstantGluing`: Gluing functions with locally constant differences.
* `Topology.CompactExhaustion`: Compact exhaustions of open subsets.
* `Topology.Frontier`: Frontiers and complementary components.
* `Topology.Graph`: Graphs characterized by equations.
* `Topology.Path`: First exit of a path from an open set.
* `Topology.SeparateContinuous`: Uniform bounds for separately continuous maps.
* `Topology.UpperSemicontinuous`: Nonnegative multiples of upper semicontinuous functions.

## References

* `Topology.LocallyConstantGluing`: formal background used by this module.
* `Topology.CompactExhaustion`: formal background used by this module.
* `Topology.Frontier`: formal background used by this module.
-/
