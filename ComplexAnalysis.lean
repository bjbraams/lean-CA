/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Integral.CurveIntegral
public import ToMathlib.Analysis.Integral.CurveIntegral.Improper
public import ComplexAnalysis.HasPrimitives
public import ComplexAnalysis.HasPrimitives.Pullback
public import ComplexAnalysis.BranchLog
public import ComplexAnalysis.BranchLog.Analytic
public import ComplexAnalysis.BranchLog.Homotopy
public import ComplexAnalysis.ExteriorPath
public import ComplexAnalysis.ExteriorPath.Integral
public import ComplexAnalysis.CauchyDerivatives
public import ComplexAnalysis.CauchyEstimates
public import ComplexAnalysis.CauchyFormula
public import ComplexAnalysis.CauchyIntegral
public import ComplexAnalysis.CauchyPompeiu
public import ComplexAnalysis.CauchySeries
public import ComplexAnalysis.CauchyTransform
public import ComplexAnalysis.CurveIndex
public import ComplexAnalysis.CurveIndex.Continuity
public import ComplexAnalysis.CurveIndex.Homotopy
public import ComplexAnalysis.HalfPlane
public import ComplexAnalysis.Injective
public import ComplexAnalysis.Integral.Circle
public import ComplexAnalysis.Integral.CirclePath
public import ComplexAnalysis.Integral.Map
public import ComplexAnalysis.Integral.Homotopy
public import ComplexAnalysis.Integral.ContinuousHomotopy
public import ComplexAnalysis.LaurentSeries
public import ComplexAnalysis.LaurentSeries.Annulus
public import ComplexAnalysis.LaurentSeries.Basic
public import ComplexAnalysis.LaurentSeries.Geometry
public import ComplexAnalysis.LocallyUniform
public import ComplexAnalysis.LogDerivIntegral
public import ComplexAnalysis.ParametricIntegral
public import ComplexAnalysis.PolygonIntegral
public import ComplexAnalysis.Pow
public import ComplexAnalysis.RealUniqueness
public import ComplexAnalysis.RemovableSingularity
public import ComplexAnalysis.Residue
public import ComplexAnalysis.Residue.LogDeriv
public import ComplexAnalysis.Residue.PrincipalPart
public import ComplexAnalysis.ArgumentPrinciple
public import ComplexAnalysis.Rouche
public import ComplexAnalysis.Hurwitz
public import ComplexAnalysis.FunctionSpace
public import ComplexAnalysis.Montel
public import ComplexAnalysis.Vitali
public import ComplexAnalysis.EssentialSingularity
public import ComplexAnalysis.RemovableLine
public import ComplexAnalysis.Reflection
public import ComplexAnalysis.Subharmonic
public import ComplexAnalysis.Subharmonic.Basic
public import ComplexAnalysis.Subharmonic.Convex
public import ComplexAnalysis.Subharmonic.Majorant
public import ComplexAnalysis.Subharmonic.SmoothCriterion
public import ComplexAnalysis.Subharmonic.Submean
public import ComplexAnalysis.UnivalentDisk
public import ComplexAnalysis.ZeroPersistence
public import ComplexAnalysis.HolomorphicIntegral
public import ComplexAnalysis.Cycle
public import ComplexAnalysis.Cycle.Cauchy
public import ComplexAnalysis.Cycle.Residue
public import ComplexAnalysis.Cycle.ArgumentPrinciple
public import ComplexAnalysis.Cycle.Parallelogram
public import ComplexAnalysis.Cycle.Piecewise
public import ComplexAnalysis.Runge.Kernel
public import ComplexAnalysis.Runge.Cutoff
public import ComplexAnalysis.Runge.Basic
public import ComplexAnalysis.Runge.PolePushing
public import ComplexAnalysis.Runge.Theorem
public import ComplexAnalysis.Runge.OpenSet
public import ComplexAnalysis.MittagLeffler
public import ComplexAnalysis.InfiniteProduct
public import ComplexAnalysis.WeierstrassFactor
public import ComplexAnalysis.WeierstrassProduct
public import ComplexAnalysis.DiscMobius
public import ComplexAnalysis.HolomorphicInverse
public import ComplexAnalysis.RiemannMapping
public import ComplexAnalysis.DiscAutomorphism
public import ComplexAnalysis.Cayley
public import ComplexAnalysis.Harnack
public import ComplexAnalysis.DirichletDisc
public import ComplexAnalysis.LocalMapping
public import ComplexAnalysis.ResidueAtInfinity
public import ComplexAnalysis.AnalyticContinuation
public import ComplexAnalysis.AnalyticOrder
public import ComplexAnalysis.NaturalBoundary
public import ComplexAnalysis.CanonicalProduct
public import ComplexAnalysis.CanonicalProduct.Bounds
public import ComplexAnalysis.CanonicalProduct.GoodRadii
public import ComplexAnalysis.FiniteOrder
public import ComplexAnalysis.Hadamard
public import ComplexAnalysis.Blaschke
public import ComplexAnalysis.HarmonicLimit
public import ComplexAnalysis.Perron
public import ComplexAnalysis.Perron.Barrier
public import ComplexAnalysis.Parseval
public import ComplexAnalysis.DiscCauchyTransform
public import ComplexAnalysis.AreaTheorem
public import ComplexAnalysis.Koebe
public import ComplexAnalysis.RieszFactorization
public import ComplexAnalysis.SchwarzPick
public import ComplexAnalysis.ThreeCircles
public import ComplexAnalysis.GreenFunction
public import ComplexAnalysis.KoebeDistortion
public import ComplexAnalysis.KoebeGrowth
public import ComplexAnalysis.MobiusGeometry
public import ComplexAnalysis.EllipticLiouville
public import ComplexAnalysis.PringsheimVivanti
public import ComplexAnalysis.SokhotskiPlemelj
public import ComplexAnalysis.PaleyWiener
public import ComplexAnalysis.CircleReflection
public import ComplexAnalysis.ChordalMetric
public import ComplexAnalysis.SphericalDerivative
public import ComplexAnalysis.EllipticResidue

/-!
# Single-variable complex analysis

General complex analysis supporting contour representations and analytic continuation.
The development extends Mathlib's complex-analysis infrastructure, with Banach-valued targets
where appropriate. Complex-specific declarations use `Complex`; extensions of existing APIs
retain their usual namespaces. General support is imported from the independent `Analysis`
and `Topology` libraries.

## Main results

* `HalfPlane`, `Pow`: right-half-plane geometry, sector roots, finite-family containing disks,
  and multiplication and holomorphy of principal powers.
* `BranchLog`: holomorphic logarithms and roots on simply connected open sets, with
  normalization and uniqueness of logarithm branches.
* `BranchLog.Homotopy`: continuous logarithm lifts of path homotopies in the punctured plane
  and invariance of the terminal branch value under continuous deformation.
* `ExteriorPath`, `ExteriorPath.Integral`: compactified paths escaping to infinity,
  their Jacobians, and Banach-valued endpoint formulas for exact exterior integrals.
* `ToMathlib.Analysis.Integral.CurveIntegral`: the general endpoint formulas for exact one-forms,
  imported by the complex curve-integral theory.
* `HasPrimitives`: Banach-valued primitives on simply connected open domains, local-to-global
  exactness, normalization, uniqueness, and the global primitive consequence of Morera's theorem.
* `HasPrimitives.Pullback`: continuous potentials after pullback along maps from simply
  connected spaces, with local primitive increments computing image-path integrals.
* `CauchyIntegral`: path independence, Cauchy's theorem on simply connected open sets, and
  integration of logarithmic derivatives.
* `CauchyFormula`: Banach-valued Cauchy formulas on simply connected open sets, with an explicit
  scalar kernel integral.
* `LogDerivIntegral`, `CurveIndex`: the exponential endpoint identity, integer-valued index
  for closed C¹ curves avoiding the pole, index laws, and the index-weighted Cauchy formula.
* `CurveIndex.Continuity`: continuity and local constancy away from the curve, constancy on
  connected components, and vanishing on unbounded components of the complement.
* `Integral.Homotopy`, `CurveIndex.Homotopy`: Cauchy's theorem under `C²` path homotopies
  on arbitrary open domains; the curve index also respects continuous based homotopies of `C¹`
  loops.
* `Integral.ContinuousHomotopy`: Cauchy's theorem under continuous homotopies, including moving
  endpoints, and passage to limits of finite contours when endpoint-track integrals vanish.
* `Integral.CirclePath`: smooth circles as paths and agreement of curve and circle integrals;
  `CurveIndex` evaluates the index inside and outside a circle.
* `Integral.Map`, `UnivalentDisk`: holomorphic changes of variables, embedded image-circle
  boundaries, two-component separation, index normalization, Banach-valued Cauchy formulas,
  and relatively compact exhaustions for domains parametrized by injective holomorphic disk maps.
* `PolygonIntegral`: integration over oriented polygon edges and polygonal Cauchy's theorem.
* `CauchyDerivatives`, `CauchyEstimates`, `CauchySeries`: circle derivative formulas, compact
  derivative bounds, geometric Taylor-coefficient majorants, and Cauchy-series estimates.
* `LaurentSeries`: Banach-valued coefficients and expansions, annular formulas, and geometry.
* `Residue`, `Residue.LogDeriv`: residues at isolated singularities, pole computations,
  and logarithmic-derivative residues equal to meromorphic orders.
* `ArgumentPrinciple`, `Rouche`, `Hurwitz`: disk zero counting with multiplicities,
  stability under perturbation, and zero-free or injective limits of holomorphic functions.
* `FunctionSpace`, `Montel`, `Vitali`: compact-open holomorphic spaces, compactness and
  convergent subsequences under compact-local bounds, and Vitali convergence from an
  interior accumulation point, using shared `Analysis` foundations without SCV imports.
* `EssentialSingularity`: analytic extension of bounded punctured germs, the isolated
  singularity alternatives, and Casorati–Weierstrass density near essential singularities.
* `Subharmonic`: planar submean and maximum principles, majorants, convex examples, and the
  Laplacian criterion.
* `CauchyPompeiu`, `CauchyTransform`: planar integral identities and transforms with parameters.
* `RemovableSingularity`, `Injective`, `ZeroPersistence`: planar removal, injectivity (with the
  circle integral of `f' / (f - f w)`), and zeros.
* `ParametricIntegral`, `RealUniqueness`, `LocallyUniform`, `Integral.Circle`: one-variable
  integration, uniqueness, convergence, and circle helpers.
* `HolomorphicIntegral`: holomorphy of parametric interval integrals with jointly continuous
  integrands, Fubini for interval integrals, and joint continuity of the divided slope.
* `Cycle`, `Cycle.Cauchy`, `Cycle.Residue`, `Cycle.ArgumentPrinciple`: cycles as finite
  families of closed `C¹` curves, their integrals and indices, and the homology forms of
  Cauchy's theorem and formula (Dixon's proof), of the residue theorem, and of the argument
  principle for cycles whose index vanishes outside the domain.
* `Cycle.Piecewise`: closed curves made of `C¹` pieces meeting at corners (polygons, rectangles,
  keyhole contours) as `C¹` cycles, by smooth concatenation; Cauchy's theorem and formula and
  the residue theorem for such curves, stated in terms of integrals over the pieces.
* `Cycle.Parallelogram`: the boundary of a parallelogram as the closed polygon through its
  vertices (`Cycle.Piecewise`), with curve integrals as sums of straight edge integrals and its
  index
  shown to vanish outside the closed parallelogram by a convexity-coning nullhomotopy and
  to equal `1` in the open interior when the edge vectors are positively oriented.
* `Runge.Kernel`, `Runge.Cutoff`, `Runge.Basic`, `Runge.PolePushing`, `Runge.Theorem`:
  Runge's approximation theorem, through the Cauchy–Pompeiu representation with a smooth
  cutoff, uniform approximation of Cauchy-type integrals by finite pole sums, and pole pushing
  in the components of the complement; polynomial approximation when the complement is
  connected.
* `Runge.OpenSet`, `MittagLeffler`: Runge's theorem on open sets through hole-free compact
  exhaustions, with locally uniformly convergent sequences of approximants, and the
  Mittag-Leffler theorem on arbitrary open sets.
* `AnalyticOrder`: finiteness of orders, finiteness and countability of zero sets, dividing out
  zeros, and division by functions with the same orders of vanishing.
* `InfiniteProduct`, `WeierstrassFactor`, `WeierstrassProduct`: holomorphy, zeros, and orders of
  locally uniformly convergent infinite products, the elementary factors with their uniform
  estimate, the Weierstrass product with prescribed zeros, and the factorization of entire
  functions.
* `DiscMobius`, `HolomorphicInverse`, `RiemannMapping`, `DiscAutomorphism`, `Cayley`: disc
  Möbius transformations, holomorphic inverses of injective holomorphic maps, the Riemann
  mapping theorem by the extremal argument, the classification of disc and half-plane
  automorphisms, and uniqueness of the normalized Riemann map.
* `Harnack`, `DirichletDisc`: Poisson kernel bounds and Harnack's inequality, the Poisson
  integral of continuous boundary data as the solution of the Dirichlet problem on a disc,
  harmonic functions as subharmonic functions, and uniqueness by the maximum principle.
* `LocalMapping`, `ResidueAtInfinity`: the local `m`-to-one mapping theorem by Rouché, the
  residue at infinity with the inversion change of variables, and the total residue theorem.
* `AnalyticContinuation`, `NaturalBoundary`: function elements along a path, uniqueness of
  analytic continuation by the clopen argument, and the lacunary series `∑ z ^ (2 ^ n)` with
  the unit circle as natural boundary.
* `CanonicalProduct`, `CanonicalProduct.Bounds`, `CanonicalProduct.GoodRadii`, `FiniteOrder`,
  `Hadamard`: canonical products of finite genus over a countable index type with their
  zeros, lower bounds off small discs around the zeros and good radii; entire functions of
  finite order, Jensen's zero-counting bound and the summability of inverse powers of the
  zeros; Hadamard's factorization theorem.
* `Blaschke`: Blaschke factors and products on the disc with their zeros and the bound by
  one, the Blaschke condition for the zeros of bounded holomorphic functions from Jensen's
  formula, and the resulting uniqueness theorem.
* `RieszFactorization`: the multiplicity-weighted Blaschke condition, division by a
  matching-order function on the disc, and the Riesz factorization theorem `f = z ^ m * B * g`
  with `B` the Blaschke product of the zeros of `f` and `g` holomorphic and nonvanishing.
* `SchwarzPick`: the Schwarz–Pick lemma in distance and derivative form, contracting the
  pseudo-hyperbolic distance and the hyperbolic metric of the disc.
* `ThreeCircles`: Hadamard's three-circle theorem, that the maximum modulus of a holomorphic
  function on a closed annulus is a log-convex function of the radius, deduced from Mathlib's
  three-lines theorem through the exponential map.
* `GreenFunction`: existence and nonnegativity of the Green function of a bounded open set with
  the exterior disc property, as the harmonic compensator for the logarithmic singularity at a
  pole.
* `KoebeDistortion`: the pre-Schwarzian bound for injective holomorphic maps of the disc, by
  Bieberbach's theorem applied to the Koebe transform at each point.
* `KoebeGrowth`: the Koebe distortion theorem (both bounds on `‖f' z‖`) and the growth theorem's
  upper bound on `‖f z‖`, by integrating the pre-Schwarzian bound along a ray through a
  holomorphic logarithm of `f'`; the growth theorem's lower bound is not derived.
* `MobiusGeometry`: invariance of the cross ratio under Möbius transformations, and generalized
  circles (circles and lines) mapping to generalized circles, by decomposing a Möbius map into
  translations, scalings, and inversion.
* `EllipticLiouville`: Liouville's first theorem for elliptic functions, that an entire
  function doubly periodic with respect to a lattice (`PeriodPair`) is constant, by showing
  it is bounded on the compact fundamental parallelogram and applying the classical Liouville
  theorem for bounded entire functions.
* `PringsheimVivanti`: the Pringsheim–Vivanti theorem, that a power series with nonnegative
  coefficients and finite positive radius of convergence `R` cannot be continued holomorphically
  across the positive real boundary point `R`, by an explicit Taylor recentering at a nearby
  point with manifestly nonnegative coefficients.
* `SokhotskiPlemelj`: the Sokhotski–Plemelj jump relation for the Cauchy-type contour integral
  of a density on a circle given by an absolutely summable two-sided Laurent series, identifying
  the interior and exterior Cauchy-type integrals with explicit one-sided power series in the
  Laurent coefficients whose difference at the boundary recovers the density.
* `PaleyWiener`: the holomorphic-extension half of the Paley–Wiener theorem, that the
  Fourier-type transform of a function integrable on `[-τ, τ]` extends to an entire function of
  exponential type at most `τ`, by differentiating under the integral sign in the complex
  parameter and an elementary growth estimate on the kernel.
* `CircleReflection`: the Schwarz reflection principle across a circle `‖z‖ = r`, the first
  genuinely curved instance of reflection across an analytic arc, by reducing to
  `Reflection`'s real-axis case via a Cayley-type Möbius map conjugating circle inversion to
  complex conjugation.
* `ChordalMetric`: the chordal (spherical) metric on `ℂ ∪ {∞}` (`OnePoint ℂ`), defined as the
  Euclidean distance between the images of two points under inverse stereographic projection
  onto the unit sphere in `ℝ³`, which gives every metric-space axiom for free from the ambient
  Euclidean metric; the classical closed-form formula is recovered as a theorem.
* `SphericalDerivative`: the spherical derivative `f#(z) = ‖f' z‖ / (1 + ‖f z‖²)`, the local
  chordal-metric distortion factor of a holomorphic function, and its invariance under the
  inversion `w ↦ 1/w`.
* `EllipticResidue`: the boundary integral of a doubly periodic function, continuous on the
  boundary, over a period parallelogram vanishes, by cancellation of opposite edges — one is
  the periodic translate of the other, traversed oppositely. Combined with
  `curveIndex_parallelogramLoop_eq_one`/`_eq_zero` (`Cycle.Parallelogram`), this is the
  elementary half of Liouville's second and third theorems for elliptic functions; assembling
  the two into those theorems (via the residue theorem/argument principle for cycles) is not
  done here.
* `HarmonicLimit`, `Perron`, `Perron.Barrier`: locally uniform limits of harmonic functions
  are harmonic, Harnack's principle for monotone sequences, the maximum principle for
  subharmonic functions with boundary upper limits, Perron's method (the upper envelope of
  the Perron family is harmonic), barriers and the boundary behaviour of the Perron
  solution, the exterior disc criterion, and the solution of the Dirichlet problem on
  bounded open sets with the exterior disc property.
* `Parseval`, `DiscCauchyTransform`, `AreaTheorem`, `Koebe`: Cauchy's coefficient formula and
  Parseval's identity for Taylor coefficients on circles with Gutzmer's inequality, the Cauchy
  transform of a disc by polar coordinates, the index-area identity and Gronwall's area theorem
  for the class `Σ`, Bieberbach's bound `‖a₂‖ ≤ 2` and the Koebe one-quarter theorem.

The index of merely continuous closed curves and the general Jordan curve theorem are not
developed here. The separation and index results above concern analytic disk contours. The
Riemann mapping theorem now supplies an injective holomorphic disk parametrization of every
simply connected proper planar domain; transporting contours through it is not yet done.

## References

* `ToMathlib.Analysis.Integral.CurveIntegral`: formal background used by this module.
* `ToMathlib.Analysis.Integral.CurveIntegral.Improper`: formal background used by this module.
* `ComplexAnalysis.HasPrimitives`: formal background used by this module.
-/
