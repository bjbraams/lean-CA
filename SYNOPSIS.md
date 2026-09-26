# Mathematical synopsis

This library formalizes foundations of complex analysis of one variable in Lean 4. Its main
results include global Cauchy and residue theory, Runge approximation and Mittag-Leffler,
normal families and the Riemann mapping theorem, entire-function factorization, and selected
parts of univalent-function and potential theory. It grew out of work on Carlson's special
functions and is now an independent library intended for contribution to Mathlib.

The account below describes the current theorem statements. [STRUCTURE.md](STRUCTURE.md)
gives the Lean interfaces and module map. The reference comparison at the end indicates
mathematical overlap, without claiming complete formalization of any textbook or its exercises.

## Foundations and conventions

Mathlib supplies complex arithmetic, differentiation and power series, the identity and maximum
principles, local Cauchy theory, removable singularities, Liouville's theorem, Schwarz's lemma,
and basic meromorphic-function theory. It also supplies Jensen's formula, Borel–Carathéodory,
Poisson representation, and Phragmén–Lindelöf estimates. The project extends these foundations.

Domains are open subsets of the complex plane; connectedness or simple connectedness is
assumed when needed. Functions are complex-valued unless another target is specified.
Much of the integration, Cauchy, Laurent, and residue theory admits values in a complex Banach
space. The normal-family compactness results require finite-dimensional targets.

## Integration, singularities, and zeros

A holomorphic Banach-valued function on a simply connected domain has a primitive. Consequently
its contour integrals depend only on endpoints. A nonvanishing scalar holomorphic function on
such a domain has a holomorphic logarithm and roots, with normalization and uniqueness.
Cauchy's theorem also holds under continuous path homotopies with suitable boundary-path
regularity; moving endpoints contribute their own integrals. The improper-integral results
state explicit convergence or vanishing conditions.

The winding number of a closed $C^1$ curve is integer-valued, locally constant off the curve,
zero on unbounded complementary components, and invariant under based homotopies avoiding
the point. For a finite $C^1$ cycle $\Gamma$ in $U$ whose index vanishes outside $U$, the library
proves the homological Cauchy theorem and formula. The corresponding residue theorem gives

$$
\int_\Gamma f(z)\,dz
=2\pi i\sum_{a\in S} n(\Gamma,a)\mathrm{Res}(f,a),
$$

where $S$ is a finite set of isolated singularities and the contour avoids $S$. Essential
singularities are allowed. The library also proves the total residue identity including infinity.

Laurent expansions on annuli, coefficient estimates, independence from the integration radius,
and pole formulas connect residues to local series. The isolated-singularity theory includes
Casorati–Weierstrass and the removable/pole/essential alternatives. The argument principle counts
zeros minus poles with multiplicity, on discs and on cycles. Rouché and Hurwitz give stability
of zero counts and the zero-free-or-identically-zero and constant-or-injective alternatives for
locally uniform limits. The local mapping theorem states that a zero of order $m$ of
$f-f(a)$ produces exactly $m$ simple preimages of every sufficiently close value other than
$f(a)$ in a sufficiently small disc.

## Convergence, approximation, and prescribed singularities

The library constructs complete spaces of holomorphic functions with the topology of uniform
convergence on compact subsets and proves convergence of all iterated derivatives under
locally uniform convergence. Montel's theorem gives compactness and convergent subsequences
for families bounded on each compact subset. Vitali's theorem gives convergence throughout a
connected domain from such bounds and pointwise convergence on a set with an interior
accumulation point.

Runge's theorem approximates a function holomorphic near a compact set $K$ by rational
functions with poles in a prescribed set meeting every bounded component of $\mathbb C\setminus K$.
When the complement is connected, polynomials suffice. Open-set versions provide locally
uniformly convergent sequences of approximants. These statements assume holomorphy on a
neighborhood of $K$; they do not assert Mergelyan's theorem.

Mittag-Leffler is proved on arbitrary open sets for a discrete set of prescribed singularities.
The input at each point may be any function holomorphic away from that point; the constructed
function differs from it by a holomorphic germ. Finite principal parts give the usual
meromorphic version. Cauchy–Pompeiu and a Cauchy transform solving $\bar\partial u=g$ for
compactly supported $C^1$ data provide the integral tools behind the approximation theory.

## Products and growth

The project proves convergence, holomorphy, zeros, and multiplicities of suitable infinite
products. Weierstrass products realize prescribed nonzero zeros tending to infinity, and an
entire function with those zeros and multiplicities and nonzero value at the origin factors
as the product times the exponential of an entire function.

The finite-order development uses an explicit growth hypothesis

$$
|f(z)|\le A\exp(B|z|^\rho),\qquad A,B\ge0.
$$

For a nonzero entire $f$ satisfying this bound with $0\le\rho<k+1$, Hadamard factorization
constructs its nonzero zeros $a_j$, counted with multiplicity, an integer $m\ge0$, and a
polynomial $P$ of degree at most $k$, such that

$$
f(z)=e^{P(z)}z^m\prod_j E_k(z/a_j),\qquad
\sum_j |a_j|^{-(k+1)}<\infty.
$$

Finite and empty zero families are included. The growth predicate is an explicit bound at a
chosen exponent, rather than a definition of order as an infimum of exponents.

On the unit disc, Blaschke products have the prescribed zeros and multiplicities whenever
$\sum_j(1-|a_j|)<\infty$. Conversely, the zeros of a nonzero bounded holomorphic function
satisfy the multiplicity-weighted Blaschke condition. The bounded-function Riesz factorization
writes $f=z^mBg$, with $g$ holomorphic, nonvanishing, and bounded by the same constant as $f$.
This does not include the full inner–outer factorization theory of Hardy spaces.

The three-circles inequality is proved for Banach-valued functions holomorphic on an open
annulus and continuous on its closure, with no nonvanishing hypothesis.

## Conformal mapping and univalent functions

Every nonempty simply connected proper plane domain has a conformal bijection onto the unit
disc. Prescribing the image of one point to be zero and its derivative to be positive real
makes the map unique. The library classifies disc and half-plane automorphisms and proves
both the distance and derivative forms of Schwarz–Pick.

Injective holomorphic images of smaller closed discs have simple boundary contours with
index one inside and zero outside, exactly two complementary components, and the normalized
Cauchy formula. These images also give compact exhaustions. This is a separation theorem for
these analytic contours, not a proof of the general Jordan curve theorem.

For normalized univalent functions $f(0)=0$, $f'(0)=1$ on the unit disc, the area theorem
leads to the second-coefficient bound $|a_2|\le2$ and Koebe's quarter theorem. The derivative
and growth estimates proved are, for $r=|z|<1$,

$$
\frac{1-r}{(1+r)^3}\le |f'(z)|\le\frac{1+r}{(1-r)^3},
\qquad |f(z)|\le\frac{r}{(1-r)^2}.
$$

The lower growth estimate is not yet included. Neither the general Bieberbach coefficient
theorem nor boundary extension of Riemann maps to arbitrary Jordan boundaries is asserted.

## Harmonic functions and boundary behavior

The Poisson integral solves the Dirichlet problem on a disc for continuous boundary data,
with uniqueness. Harnack's inequality, harmonicity of locally uniform limits, and Harnack's
monotone convergence principle are proved. Subharmonic functions here are finite real-valued
upper semicontinuous functions satisfying a local submean inequality. The theory includes
maximum principles, the submean inequality on all contained closed discs for continuous
subharmonic functions, holomorphic examples, and the $C^2$ criterion $\Delta u\ge0$.

Perron's construction gives a harmonic envelope on a bounded open set for bounded boundary
data. Barriers imply attainment of continuous data at the corresponding boundary points.
In particular, the Dirichlet problem is solved when every boundary point $\zeta$ has an
exterior closed disc meeting the closure of the domain only at $\zeta$. Under this condition,
the library constructs a nonnegative Green function with zero boundary limits and the
logarithmic singularity at its pole. Symmetry and strict positivity are not established.

Removability under continuity covers countable sets, analytic zero sets, and gluing across
the real axis. Schwarz reflection covers the real axis and circles, the latter on suitable
inversion-invariant domains avoiding the coordinate poles. Analytic continuation is unique
along a fixed path; general monodromy remains outside the development. The series
$\sum_{n\ge0}z^{2^n}$ is shown to have the unit circle as a natural boundary. Pringsheim–Vivanti
is proved in the form that a holomorphic extension across the positive boundary point of a
nonnegative-coefficient power series forces convergence at a larger positive real argument.

## Selected further results and limits of scope

There are cross-ratio identities for Möbius maps, chordal-distance formulas on the extended
plane, and inversion invariance of the spherical derivative. These do not yet supply a
normal-family theory for meromorphic maps or Marty's criterion.

The circle Sokhotski–Plemelj result identifies the interior and exterior Cauchy integrals with
their series for absolutely summable Laurent boundary data and proves the jump identity for
those series values. Explicit one-sided limit and principal-value statements remain absent.
The Paley–Wiener development gives entire extension and an exponential-type bound for the
Fourier-type transform of integrable data supported in a bounded interval; it does not prove
the full $L^2$ characterization.

Entire doubly periodic functions are constant. The period-parallelogram index and cancellation
of opposite-edge integrals are also proved, but cancellation currently assumes global
continuity. The meromorphic residue-sum and equal-zero/pole-count theorems for elliptic
functions remain unassembled.

Other substantial topics in the references that this library does not develop include Picard,
Bloch and Schottky theorems, general reflection across analytic arcs, Schwarz–Christoffel
mapping, prime ends and conformal classification of multiply connected domains, general
Weierstrass zero prescription on open sets, and logarithmic capacity and fine potential theory.
Textbook collections of evaluated contour integrals and special-function applications are not
systematically reproduced.

## Relation to the references

The comparison uses the editions and chapter ranges listed at the start of
[COVERAGE.md](COVERAGE.md), with selected later chapters where the library goes further.
The local PDFs are in `ComplexAnalysis/References`. The summaries concern the mathematical
content of the statements, not identity of proof or complete chapter coverage.

| Reference and comparison range | Relationship to this library and Mathlib |
| --- | --- |
| [Agarwal–Perera–Pinelas, *An Introduction to Complex Analysis* (2011)](ComplexAnalysis/References/AgarwalPereraPinelas2011IntroductionComplexAnalysis-Springer.pdf), Lectures 25–44 | Laurent theory, isolated singularities, residues, zero counting, reflection, products, and Mittag-Leffler are represented. The contour-evaluation examples and Schwarz–Christoffel transformation are not systematically covered. |
| [Bak–Newman, *Complex Analysis*, 3rd ed. (2010)](ComplexAnalysis/References/BakNewman2010ComplexAnalysis3rdEd-SpringerUTM.pdf), Chapters 4–18 | Strong overlap in Cauchy theory, singularities, conformal mapping, harmonic functions, and products. Elementary theory and Phragmén–Lindelöf come from Mathlib; mapping examples, boundary theorems, and applications extend beyond the project. |
| [Burckel, *Classical Analysis in the Complex Plane* (2021)](ComplexAnalysis/References/Burckel2021ClassicalAnalysisComplexPlane-Birkhäuser.pdf), Chapters II–VIII | Integration, index, branches, local theory, Schwarz–Pick, convergence, and Runge are represented. General Jordan separation, boundary dynamics, and specialized approximation results are not. The library also overlaps IX in Riemann mapping and XI in singularities. |
| [Conway, *Functions of One Complex Variable I*, 2nd ed. (1978)](ComplexAnalysis/References/Conway1978FunctionsOfOneComplexVariable1-SpringerGTM11.pdf), Chapters IV–XII | A close guide to global Cauchy theory, normal families, Runge, products, and finite-order factorization. Continuation and potential theory are partial as described above; the omitted-value theorems of XII are absent. |
| [Conway, *Functions of One Complex Variable II* (1995)](ComplexAnalysis/References/Conway1995FunctionsOfOneComplexVariable2-SpringerGTM159.pdf), Chapters 13–15, 20–21 | Selected overlap: reflection, the area and univalent estimates of 14 §§6–7, and bounded-function Blaschke factorization related to 20. The prime-end, multiply connected, Hardy-space, and capacity theories are not supplied. Perron and Green-function results also overlap parts of Chapter 19. |
| [Gamelin, *Complex Analysis* (2001)](ComplexAnalysis/References/Gamelin2001ComplexAnalysis-Springer.UTM.pdf), Chapters II–VII | The basic function, integration, Laurent, and residue theory is shared with Mathlib and extended here. Later overlap includes zero counting, Schwarz–Pick, Riemann mapping, approximation, and parts of the Dirichlet theory; meromorphic compactness and the full boundary theory remain outside scope. |
| [Heins, *Complex Function Theory* (1968)](ComplexAnalysis/References/Heins1968ComplexFunctionTheory-AcademicPress), Chapters IV–VIII | Cauchy theory, Laurent expansions, residues, and prescribed principal parts are represented. The general open-domain divisor-realization theory goes beyond the entire and disc product constructions here. |
| [Lang, *Complex Analysis*, 4th ed. (1999)](ComplexAnalysis/References/Lang1999ComplexAnalysis4thEd-SpringerGTM103.pdf), Chapters I–XIII | I–II are predominantly Mathlib foundations. III–VIII closely match the integration, homology, singularity, conformal, and harmonic core. IX–XI are partial: line/circle reflection, Riemann mapping, and fixed-path continuation uniqueness are present; general arc reflection, boundary extension, and monodromy are absent. XII is selective; XIII has substantial product, finite-order, and Mittag-Leffler coverage. |
| [Simon, *A Comprehensive Course in Analysis*, Part 2A (2015), companion booklet](ComplexAnalysis/References/Simon2015ComprehensiveCourseAnalysisCompanion-AMS.pdf), Chapters 2–4 | The chapter topics align with local Cauchy theory, singularities, indices, homological Cauchy theory, and Runge. The available PDF contains contents and indices, not the text of Part 2A, so this is a topic-level comparison only. |
| [Stein–Shakarchi, *Complex Analysis* (2003)](ComplexAnalysis/References/SteinShakarchi2003PrincetonLecturesAnalysis2ComplexAnalysis-PrincetonUniversityPress.pdf), Chapters 2–3 | Cauchy theory, branches, residues, and the argument principle are represented, using Mathlib for much of the local foundation. Further overlap includes finite-order factorization in Chapter 5 and Riemann mapping in Chapter 8; the Chapter 4 Paley–Wiener result is partial. |
| [Remmert, *Theory of Complex Functions* (1991)](ComplexAnalysis/References/Remmert1991TheoryOfComplexFunctions-SpringerGTM122.pdf), Chapters 6–8 | Integration, primitives, Cauchy estimates, convergence, and local mapping theory are covered jointly with Mathlib. The project emphasizes general interfaces rather than the book's historical material and worked examples. |

For Lang XII in particular, Jensen, Borel–Carathéodory, and Phragmén–Lindelöf are Mathlib
inputs; the project adds the three-circles theorem above. Picard–Borel, the Hermite
interpolation formula, and the arithmetic applications are not supplied by this project.
For XIII §3, the explicit growth-bound formulation of Hadamard factorization should be
compared with Lang's distinction between order and strict order.
