# Library structure

This is a guide for Lean maintainers. The mathematical scope and reference comparison are in
[SYNOPSIS.md](SYNOPSIS.md); [README.md](README.md) is the project entry point.
The library develops complex analysis of one variable on top of Mathlib, with general support
kept separate from the complex-specific results.

## Package and imports

Lean and Mathlib are pinned to `v4.35.0-rc2` in [lean-toolchain](lean-toolchain) and
[lakefile.toml](lakefile.toml). The Lake package and default library target are named `LeanCA`.
The three source roots have matching umbrella modules:

| Root | Role | Project dependencies |
| --- | --- | --- |
| [Topology](Topology.lean) | Gluing, frontiers, simple connectedness of convex sets, and semicontinuity | None |
| [Analysis](Analysis.lean) | Differentiation, integration, normed-space tools, and holomorphic function spaces | None outside `Analysis` |
| [ComplexAnalysis](ComplexAnalysis.lean) | Function theory of one complex variable | `Analysis`, `Topology` |

All three use Mathlib. [LeanCA.lean](LeanCA.lean) imports their umbrellas. `ComplexAnalysis` has no
import dependency on Carlson applications, several complex variables, or simplex integration.
For downstream use, import the individual
topic modules needed, or `ComplexAnalysis` for the complete complex-analysis library.

Run `lake build` from this directory. The intentional `.lake` symlink points to
`/export/scratch1/braams/lean-codes-lake`; preserve it and the existing toolchain pins.
See [AGENTS.md](AGENTS.md) for editing and validation requirements.

## Main interfaces

Declarations generally extend Mathlib namespaces: `Complex`, `AnalyticOnNhd`, `DiffContOnCl`,
`MeasureTheory`, and the relevant topological or algebraic structures. There is no separate
project-wide namespace or replacement definition of holomorphy. Common inputs are
`DifferentiableOn ℂ f U`, `AnalyticOnNhd ℂ f U`, and `DiffContOnCl ℂ f U`; openness and
boundary regularity must be read from each statement.

Contour integration uses Mathlib's `curveIntegral` and `circleIntegral`. A function `f : ℂ → F`
is integrated as the one-form `fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)`.
The primitive, Cauchy, Laurent, and residue APIs allow complex Banach targets where indicated.
Zero counting, conformal mapping, and factorization use scalar-valued functions.

`Complex.Cycle` represents a finite family of closed paths. The homological Cauchy and residue
theorems impose `IsC1`, containment of the cycle range, and vanishing of its index outside the
domain. They do not require a chosen Jordan interior or a homology-group construction.
Piecewise-`C¹` closed curves enter through `Loop.piecewise` and `Loop.polygon` (`Cycle.Piecewise`),
built on `Path.smoothConcat` (`Analysis.Integral.CurveIntegral.SmoothConcat`); the corresponding
Cauchy and residue theorems are stated with integrals over the pieces.
Meromorphic orders and divisors use Mathlib's APIs.

`Complex.HolomorphicMap` in `Analysis.Holomorphic.FunctionSpace` carries the compact-open
structure. `Analysis.Holomorphic.NormalFamily` takes closedness and uniqueness hypotheses as
inputs; `ComplexAnalysis.FunctionSpace`, `Montel`, and `Vitali` supply the one-variable
specializations. Compactness and the stated Vitali theorems require finite-dimensional targets.
`Complex.SubharmonicOn` is real-valued: it does not admit the value `−∞`.

## Where to work

Module names in this table are relative to `ComplexAnalysis`. A name ending in `/` denotes a
family of modules; consult its source files for the individual declarations.

| Development | Main modules | Interface and dependencies |
| --- | --- | --- |
| Primitives and branches | `HasPrimitives`, `HasPrimitives/Pullback`, `BranchLog`, `BranchLog/` | Local-to-global primitives use `Topology.LocallyConstantGluing`; logarithms use Mathlib covering-space machinery. Includes normalized logarithms, roots, parameter dependence, and homotopy lifts. |
| Contours and Cauchy theory | `CauchyIntegral`, `CauchyFormula`, `CurveIndex`, `CurveIndex/`, `Integral/`, `Cycle`, `Cycle/`, `PolygonIntegral` | Endpoint and deformation identities, winding numbers, and Cauchy theory on simply connected sets and null-homologous cycles. |
| Local theory and residues | `CauchyDerivatives`, `CauchyEstimates`, `CauchySeries`, `LaurentSeries`, `LaurentSeries/`, `Residue`, `Residue/`, `ResidueAtInfinity`, `EssentialSingularity` | Banach-valued expansions and estimates; isolated singularities, principal parts, and residues, including infinity. |
| Zeros and convergence | `ArgumentPrinciple`, `Rouche`, `Hurwitz`, `Injective`, `ZeroPersistence`, `LocalMapping`, `LocallyUniform`, `FunctionSpace`, `Montel`, `Vitali` | Divisor counts, local multiplicity, persistence of zeros, derivative convergence, and normal families. |
| Approximation | `CauchyPompeiu`, `CauchyTransform`, `Runge/`, `MittagLeffler` | Cauchy transforms and cutoffs feed Runge approximation; compact exhaustions give open-set approximation and prescribed principal parts. Main endpoints: `runge`, `runge_isOpen`, `mittagLeffler`. |
| Entire functions | `AnalyticOrder`, `InfiniteProduct`, `WeierstrassFactor`, `WeierstrassProduct`, `CanonicalProduct`, `CanonicalProduct/`, `FiniteOrder`, `Hadamard` | Shared order and division lemmas for analytic functions on preconnected open sets; product convergence and multiplicities, zero counting, lower bounds on suitable circles, and `exists_hadamard_factorization`. |
| Bounded disc functions | `Blaschke`, `RieszFactorization` | Blaschke products and the necessary zero condition; `exists_rieszFactorization` constructs the zero family and a bounded nonvanishing cofactor. |
| Conformal mapping | `DiscMobius`, `Cayley`, `HolomorphicInverse`, `DiscAutomorphism`, `RiemannMapping`, `SchwarzPick`, `UnivalentDisk/` | Disc and half-plane maps, `exists_riemannMap`, normalized uniqueness, Schwarz–Pick, and contour geometry and exhaustions for univalent disc images. |
| Univalent estimates | `Parseval`, `DiscCauchyTransform`, `AreaTheorem`, `Koebe`, `KoebeDistortion`, `KoebeGrowth` | Area theorem, second-coefficient bound, quarter theorem, pre-Schwarzian bound, both derivative distortion bounds, and upper growth bound. |
| Potential theory | `Subharmonic/`, `Harnack`, `DirichletDisc`, `HarmonicLimit`, `Perron`, `Perron/Barrier`, `GreenFunction` | Submean and maximum principles, Poisson solutions, harmonic limits, Perron envelopes, boundary barriers, and Green functions. |
| Continuation and boundary phenomena | `RemovableSingularity`, `RemovableLine`, `Reflection`, `CircleReflection`, `AnalyticContinuation`, `NaturalBoundary`, `PringsheimVivanti` | Removal and reflection, uniqueness along a fixed path, an explicit natural boundary, and the positive-coefficient boundary singularity theorem. |
| Further interfaces | `ThreeCircles`, `MobiusGeometry`, `ChordalMetric`, `SphericalDerivative`, `SokhotskiPlemelj`, `PaleyWiener`, `EllipticLiouville`, `EllipticResidue` | The three-circles theorem (via Mathlib's three-lines theorem) and selected geometric, boundary-integral, Fourier-transform, and periodic-function results; scope restrictions below. |

`Analysis.Integral` contains the general pullback and improper-integral endpoint formulas.
`ExteriorPath` and `ExteriorPath/Integral` specialize these tools to complex paths escaping to
infinity. `ParametricIntegral` and `HolomorphicIntegral` handle complex parameter integrals;
`HalfPlane`, `Pow`, and `RealUniqueness` supply branch geometry and uniqueness tools.

## Boundaries of the current APIs

The theorem statements, rather than filenames or older module summaries, determine coverage.
The following distinctions matter when reusing results or preparing an upstream contribution:

- `HasOrderLE f ρ` means an explicit bound `‖f z‖ ≤ A * exp (B * ‖z‖ ^ ρ)`.
  It is not defined as the classical infimum of growth exponents. Hadamard factorization
  assumes this bound with `0 ≤ ρ < k + 1` and gives a polynomial exponent of degree at most `k`.
  `exists_hadamard_factorization` constructs a countable zero family, allowing finite and empty
  families; the earlier `hadamard_factorization` takes that family as input.
- `exists_rieszFactorization` includes zeros at the origin and constructs the remaining zeros
  with multiplicity. Its cofactor retains the bound on the original function. This is the
  bounded holomorphic case, not the full Hardy-space inner–outer factorization theory.
- `KoebeGrowth` proves both derivative bounds and the upper growth bound. The lower growth
  bound is absent. `ThreeCircles` needs only holomorphy on the open annulus and continuity
  on its closure.
- Perron's envelope is harmonic for bounded boundary data on bounded open sets. Boundary
  attainment needs a barrier. The exterior-disc criterion requires
  `closedBall c R ∩ closure U = {ζ}`. `exists_greenFunction` uses this criterion at every
  boundary point and proves a harmonic compensator, zero boundary limits, and nonnegativity;
  symmetry and strict positivity are not included.
- `AnalyticContinuation` proves uniqueness along a fixed path. General homotopy invariance
  of analytic continuation and the monodromy theorem are not provided. Reflection covers the
  real axis and circles; the circle theorem uses an inversion-invariant open set avoiding
  `0` and the Cayley pole `−r`.
- `SokhotskiPlemelj` identifies the interior and exterior Cauchy integrals for absolutely
  summable Laurent boundary data and proves the series jump identity. It does not state the
  one-sided boundary limits or a principal-value formula. `PaleyWiener` proves entire
  extension and exponential growth for the transform of integrable compactly supported data,
  without the full `L²` characterization.
- `ChordalMetric` proves distance formulas and metric axioms for `chordalDist` on `OnePoint ℂ`;
  this is not a meromorphic normal-family API. `SphericalDerivative` supplies inversion
  invariance, not Marty's criterion.
- `MobiusGeometry` proves cross-ratio invariance and explicit transformations of generalized
  circle equations. Its assembled `isGenCircle_mobiusMap` has pointwise existential output
  coefficients and no nondegeneracy conclusion; it should not be advertised as a setwise
  circle-preservation theorem.
- `EllipticLiouville` proves constancy of entire doubly periodic functions. `EllipticResidue`
  proves cancellation for periodic functions continuous on the boundary; the meromorphic residue-sum
  and equal-zero/pole-count theorems are not assembled.

## Relationship to Mathlib and documentation

The mathematical account is [SYNOPSIS.md](SYNOPSIS.md).
Mathlib supplies the basic analytic and meromorphic APIs, local Cauchy theory, identity and
maximum principles, Liouville, Schwarz, locally uniform holomorphic limits, Jensen,
Borel–Carathéodory, Poisson representation, and Phragmén–Lindelöf. The project builds its global
contour, approximation, factorization, and mapping results on those foundations. These are
potential Mathlib contributions; inclusion here is not a claim that every auxiliary lemma is
absent from Mathlib.
