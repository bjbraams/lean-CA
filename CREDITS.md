# Related formalizations and credits

Reviewed on **24 September 2026**. This project acknowledges the formalization work
listed below. Several of its theorems also occur in these developments, sometimes
with almost identical hypotheses and conclusions. The comparisons identify useful
credits and opportunities for future consolidation with Mathlib.

This is an acknowledgment of related work, not a claim about where this project's
proofs originated. Before this review, the inspected local module documentation cited
textbooks and Mathlib infrastructure, without explicit links attributing these results
to the external formalizations below. Brief credit notes now accompany the relevant
statement docstrings; the comparisons and sources are collected here. Similar statements,
names, or classical proof strategies do not establish copying. Source authorship headers
have therefore not been changed.

## Closest theorem matches

### Riemann mapping, Hurwitz, and normal families

**Vincent Beffara — [RMT4](https://github.com/vbeffara/RMT4).**
The source contains `montel`, `hurwitz`, `hurwitz_inj`, and `RMT`.
These overlap with [Montel.lean](ComplexAnalysis/Montel.lean),
[Hurwitz.lean](ComplexAnalysis/Hurwitz.lean), and
[RiemannMapping.lean](ComplexAnalysis/RiemannMapping.lean), including the compactness
and extremal-derivative approach to the mapping theorem.
The hypothesis called `UniformlyBoundedOn` in RMT4 means boundedness on each compact
subset, so its Montel theorem is a close match to ours despite the terminology.
RMT4's `RMT` assumes that the domain has primitives, in addition to being open,
connected, and proper. Our `exists_riemannMap` instead assumes simple connectivity
and includes a base-point and positive-real-derivative normalization.
See the inspected [Montel source][rmt-montel], [Hurwitz source][rmt-hurwitz], and
[mapping theorem][rmt-main].

**Yury Kudryashov — [Mathlib PR #33505](https://github.com/leanprover-community/mathlib4/pull/33505), open draft.**
Its `exists_bijOn_unitBall_map_eq_zero` has the same open, simply connected, proper
domain hypotheses and prescribed zero as our mapping theorem; our conclusion also
normalizes the derivative. Its two Hurwitz results have exactly the same long
declaration names as ours:
`eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn` and
`eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn`.
The inspected PR requires a countably generated nontrivial filter; our versions
require only a nontrivial filter. Its
`circleIntegral_logDeriv_eq_finsum_analyticOrderNatAdd` also overlaps with the
holomorphic case of [ArgumentPrinciple.lean](ComplexAnalysis/ArgumentPrinciple.lean),
whose API uses meromorphic divisors. These are particularly appropriate credits
for the corresponding modules. [Inspected PR source][pr-rmt].

The [Zulip discussion of complex analysis][zulip-complex] connects both RMT efforts
and their supporting work. Beffara's contribution should be acknowledged separately
from Kudryashov's PR.

### Higher Cauchy formula at an interior point

**`JJYYY-JJY`, with credited coauthor `ajirving` —
[Mathlib PR #43100](https://github.com/leanprover-community/mathlib4/pull/43100), open.**
The PR's `DiffContOnCl.circleIntegral_one_div_sub_pow_smul` and our
`DiffContOnCl.iteratedDeriv_eq_circleIntegral_sub_zpow_smul` in
[CauchyDerivatives.lean](ComplexAnalysis/CauchyDerivatives.lean) express the same
Banach-valued higher Cauchy formula at an arbitrary point inside the circle, with
the equality rearranged and the kernel written differently. This is a direct
theorem-level match. The PR additionally allows a countable exceptional set in
its main differentiability hypothesis. The handles above are used to avoid
guessing names not established by the inspected attribution. [PR changes][pr-cauchy].

### Residues

**Roman Kvasnytskyi (`Periecle`) —
[Mathlib PR #29588](https://github.com/leanprover-community/mathlib4/pull/29588), open.**
Its circle-integral definition of residue, independence of radius,
`residue_of_holomorphic`, and `residue_simple_pole` closely match
`residue_eq_circleIntegral`, `AnalyticAt.residue_eq_zero`, and
`residue_sub_inv_smul` in [Residue.lean](ComplexAnalysis/Residue.lean).
The PR is scalar-valued and takes a proof of an isolated singularity as an argument
to `residue`; ours is Banach-valued and characterizes the eventual normalized circle
integral, with hypotheses attached to theorems. [Inspected source][pr-residue].

**The PrimeNumberTheoremAnd (PNT+) contributors**, and the distinct
**[Mathlib PR #39232](https://github.com/leanprover-community/mathlib4/pull/39232)**,
deserve credit for rectangular contour results. PNT+'s
`ResidueTheoremOnRectangleWithSimplePole` is an existing simple-pole contour formula
([inspected source in Cipollina's fork][pnt-residue]). PR #39232 is an open draft
submitted by `jerwaynejones`; its source header credits **Jeremy Tan**. It proves
`boundaryIntegral_eq_residue_sum` for a specified sum of simple poles and a
holomorphic remainder. These overlap with special cases of our cycle residue
theory, but should not be described as general isolated-singularity residue
theorems. [Inspected PR source][pr-rectangle].

### Weierstrass factors and Hadamard factorization

**Matteo Cipollina (`leibniz-rs`) — Hadamard development in a
[PrimeNumberTheoremAnd fork](https://github.com/leibniz-rs/PrimeNumberTheoremAnd/tree/leibniz-rs-patch-1).**
His [Zulip announcement][zulip-hadamard] led to a substantial source-level match:

- `weierstrassFactor` is the same elementary factor as our `elementaryFactor`.
  His `weierstrassFactor_sub_one_pow_bound` and our
  `norm_one_sub_elementaryFactor_le` have the same constant and range:
  `4 * ‖z‖ ^ (m + 1)` for `‖z‖ ≤ 1/2`.
- `hadamard_factorization_of_growth` factors a nonzero entire function as an
  exponential of a polynomial, an origin power, and an intrinsically indexed
  canonical product. This closely matches our `exists_hadamard_factorization`.
  His growth hypothesis bounds `log (1 + ‖f z‖)` by `C * (1 + ‖z‖)^ρ`, with
  genus and degree bounded by `floor ρ`. Ours uses `HasOrderLE f ρ` and an integer
  genus `k` with `ρ < k + 1`.
- `hadamard_factorization_of_order` also handles the epsilon-family formulation
  of order. Zero-counting and inverse-power summability results overlap with
  [FiniteOrder.lean](ComplexAnalysis/FiniteOrder.lean).

Credit this development in connection with
[WeierstrassFactor.lean](ComplexAnalysis/WeierstrassFactor.lean),
[CanonicalProduct.lean](ComplexAnalysis/CanonicalProduct.lean), and
[Hadamard.lean](ComplexAnalysis/Hadamard.lean).
The inspected [factor file][had-factor] and [factorization file][had-main] contain
proof bodies. A comment mentioning removal of a final `sorry` is historical text,
not a remaining proof hole in that file. This review did not rebuild the external
development or audit all of its dependencies.

### Cauchy–Pompeiu and the inhomogeneous Cauchy–Riemann equation

**Will (Ziang) Li — [RiemannDynamics](https://github.com/will1491/RiemannDynamics).**
Its `cauchyTransform_dzbar` proves the compactly supported
`C¹` identity `P(∂̄f) = f`, closely matching
`integral_inv_smul_dbarAlong_fderiv` in
[CauchyPompeiu.lean](ComplexAnalysis/CauchyPompeiu.lean). Its
`dzbar_cauchyTransform_eq` commutes differentiation with the transform, matching
`dbarAlong_fderiv_cauchyTransformFst` in
[CauchyTransform.lean](ComplexAnalysis/CauchyTransform.lean).
It then combines these facts in `dzbar_cauchyTransform` to obtain `∂̄(Pf) = f`.
The external version is scalar-valued; ours allows Banach-valued functions and
auxiliary parameters. Kernel signs and translations must be accounted for in any
future API comparison. [Inspected Cauchy-transform source][dyn-cauchy].

Li's open [Mathlib PR #42630](https://github.com/leanprover-community/mathlib4/pull/42630)
defines Wirtinger derivatives and proves the Cauchy–Riemann characterization.
Its antiholomorphic derivative is our `dbarAlong (fderiv ℝ f z) 1` in the scalar
case. [Inspected PR changes][pr-wirtinger].
**Stefan Kebekus** also has this operator and its holomorphic vanishing theorem,
packaged as a linear differential operator, in [Project VD][vd-wirtinger].

RiemannDynamics' [classical Montel theorem][dyn-montel] explicitly imports and
repackages Beffara's RMT4 result. Credit that dependency rather than treating it as
a third independent Montel proof.

### Montel and Vitali–Porter in the Ising-model project

**The [`phasetr/ising-model`](https://github.com/phasetr/ising-model) contributors.**
The project contains
`IsingModel.FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn`: a locally bounded
holomorphic sequence on an open preconnected domain, converging on a subset with
an interior accumulation point, converges locally uniformly to a holomorphic
function. This closely matches
`Complex.exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto` in
[Vitali.lean](ComplexAnalysis/Vitali.lean). Its accompanying
`exists_subseq_tendstoLocallyUniformlyOn_of_locallyBounded` is a close Montel match.
See the [Vitali theorem][ising-vitali] and [Montel extraction][ising-montel].

The legacy filename `FunctionTheoryAxioms.lean` is potentially misleading: at the
inspected revision it re-exports the proved Vitali theorem. The reviewed
VitaliPorter files contain proof bodies and no `sorry` or explicit axiom
declarations; this is not a validation claim about the entire Ising-model library.
No individual author is identified in those file headers, so the credit is to the
project contributors.

### Analytic logarithms and parameter integrals

**Geoffrey Irving — [ray](https://github.com/girving/ray).**
`AnalyticOnNhd.exists_log` constructs a normalized analytic logarithm of a
nonvanishing function on a disk. This is a special-domain counterpart of our
simply connected-domain results in [BranchLog.lean](ComplexAnalysis/BranchLog.lean)
and [BranchLog/Analytic.lean](ComplexAnalysis/BranchLog/Analytic.lean).
The project also has `AnalyticOnNhd.integral` and `uniform_analytic_lim`, related to
our holomorphic parameter-integral and locally uniform convergence infrastructure.
See [logarithms][ray-log], [integrals][ray-integral], and [limits][ray-uniform].
These warrant acknowledgment as overlapping analytic infrastructure; this review
does not propose replacing our more general statements with them.

## Related efforts with narrower or unfinished overlap

- **Vincent Beffara's [Curvint](https://github.com/vbeffara/Curvint)** builds a
  covering space from local holomorphic primitives and defines `ContourIntegral`
  by lifting a continuous path. This is closely related to our
  [LocallyConstantGluing.lean](Topology/LocallyConstantGluing.lean),
  [HasPrimitives.lean](ComplexAnalysis/HasPrimitives.lean), and pullback theory.
  Its `DifferentiableOn.exists_primitive` in `Primitive.lean` is a star-convex-domain
  result, not the general simply connected theorem.
  [Covering-space source][curvint-covering]; [primitive source][curvint-primitive].
- **Junyan Xu's [Mathlib PR #26950](https://github.com/leanprover-community/mathlib4/pull/26950)**
  is an open draft with substantial étalé-space and monodromy infrastructure.
  At the reviewed revision its `Analysis/Complex/Primitive.lean` contains imports
  and a description of the intended construction, but no declarations. Credit it
  as an approach and related work, not as an already implemented primitive theorem.
  [Inspected changes][pr-primitive].
- **Yury Kudryashov's [PR #33368](https://github.com/leanprover-community/mathlib4/pull/33368)**
  gives unit-disk shifts `(a + z) / (1 + conj a * z)`, overlapping our
  [DiscMobius.lean](ComplexAnalysis/DiscMobius.lean) after changing the parameter's
  sign. His open [PR #33381](https://github.com/leanprover-community/mathlib4/pull/33381)
  develops a Schwarz estimate and a separate-holomorphy application.
- **Stefan Kebekus's Project VD** supplies much of the harmonic, meromorphic,
  divisor, and Jensen infrastructure already in Mathlib. Its open PRs include
  [Poisson–Jensen #42475](https://github.com/leanprover-community/mathlib4/pull/42475),
  [positive-log circle averages #43859](https://github.com/leanprover-community/mathlib4/pull/43859),
  and [polynomial-growth Liouville #43888](https://github.com/leanprover-community/mathlib4/pull/43888).
  These are related to our subharmonic and finite-order developments, but the
  last theorem bounds the function itself, whereas our
  `exists_polynomial_of_frequently_re_le` bounds its real part on arbitrarily
  large circles. The positive-log estimate is also different from our holomorphic
  submean inequality.
- **Project VD's [PR #43985](https://github.com/leanprover-community/mathlib4/pull/43985)**
  concerns reciprocal disk factors used in Poisson–Jensen theory. Despite the
  title “canonical factors,” these are not Weierstrass elementary factors.
  Its disk-norm inequality is related to our Möbius and Blaschke factors; the
  logarithmic-derivative formulas are additional results.
- **[PR #26479](https://github.com/leanprover-community/mathlib4/pull/26479)**
  (`thefundamentaltheor3m`) develops Cauchy–Goursat for unbounded rectangles.
  This is relevant to our improper contour-deformation work, with specialized
  contours and convergence hypotheses, rather than an identical general theorem.

## Search evidence and limits

The search covered all 304 results returned for open Mathlib PRs matching
`complex`, supplemented by searches for harmonic, entire, and holomorphic work,
and searches of public Lean Zulip archives and linked repositories. Fifteen
candidate PRs had their current open/draft status checked through GitHub's API;
the closest matches were examined in source. This is a dated review, not an
exhaustive claim about all unpublished Lean code.

Particularly useful Zulip sources were the [complex-analysis discussion][zulip-complex]
and [Hadamard announcement][zulip-hadamard].
[Daniel Eriksson's Laurent/residue proposal][zulip-laurent] is a relevant lead for
our Banach-valued Laurent theory, but the discussion alone does not supply a
completed formalization. The older [argument-principle discussion][zulip-argument]
and [contour-integral discussion][zulip-contours] record further community work;
they do not by themselves establish theorem-level Lean matches.

The public archive pages consulted say they were last updated on 28 February
2026. Later conversations may therefore be missing, even though PR status and
repository snapshots were retrieved on the review date. Searches did not establish
additional completed Lean matches for our Runge, Mittag–Leffler, or Koebe
developments. The [Runge benchmark](https://lean-lang.org/eval/problems/runge_theorem/)
exposes a problem statement with `sorry`; that statement alone is not a competing
proof and does not justify a formalization credit.

Links below pin the inspected repository sources to commits. PR links describe
the review-date status; they may subsequently merge or change. External source
inspection is **not build validation**. The attribution edits change statement
docstrings only; declaration types, proofs, assumptions, and dependencies are unchanged.

[rmt-montel]: https://github.com/vbeffara/RMT4/blob/69a9efe77e912647d651aa7368856955b24dca2f/RMT4/Montel.lean
[rmt-hurwitz]: https://github.com/vbeffara/RMT4/blob/69a9efe77e912647d651aa7368856955b24dca2f/RMT4/hurwitz.lean
[rmt-main]: https://github.com/vbeffara/RMT4/blob/69a9efe77e912647d651aa7368856955b24dca2f/RMT4/Main.lean
[pr-rmt]: https://github.com/leanprover-community/mathlib4/blob/d43061d911b1aeae0788591da437a3b115098962/Mathlib/Analysis/Complex/RiemannMapping.lean
[pr-cauchy]: https://github.com/leanprover-community/mathlib4/blob/bdaa4f3ed881b13004888a59002451824e0ece24/Mathlib/Analysis/Complex/CauchyIntegral.lean
[pr-residue]: https://github.com/leanprover-community/mathlib4/blob/4d414277acd2487cec4c7946483149f8d627fb51/Mathlib/Analysis/Complex/Residue/Basic.lean
[pr-rectangle]: https://github.com/leanprover-community/mathlib4/blob/cad38f70f5a649a40dbb3b334055a8e9aff69af5/Mathlib/Analysis/Complex/RectangleResidue.lean
[pnt-residue]: https://github.com/leibniz-rs/PrimeNumberTheoremAnd/blob/8dc50485d7166be58b05ee0d54216c06a4b3aef9/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean
[had-factor]: https://github.com/leibniz-rs/PrimeNumberTheoremAnd/blob/8dc50485d7166be58b05ee0d54216c06a4b3aef9/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/WeierstrassFactor.lean
[had-main]: https://github.com/leibniz-rs/PrimeNumberTheoremAnd/blob/8dc50485d7166be58b05ee0d54216c06a4b3aef9/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/Hadamard.lean
[dyn-cauchy]: https://github.com/will1491/RiemannDynamics/blob/b3fa37cc0f18a23ea66b654ea3f73eb472129010/RiemannDynamics/Analysis/SingularIntegral/Cauchy.lean
[dyn-montel]: https://github.com/will1491/RiemannDynamics/blob/b3fa37cc0f18a23ea66b654ea3f73eb472129010/RiemannDynamics/NormalFamilies/Montel.lean
[pr-wirtinger]: https://github.com/leanprover-community/mathlib4/blob/3dcc9d658bca38edfefe8e94384b10be67431a72/Mathlib/Analysis/Complex/Wirtinger.lean
[vd-wirtinger]: https://github.com/kebekus/ProjectVD/blob/8dd096581f1578e2d0b75b099c8314a198902f1b/VD/LinearDiffOp/Wirtinger.lean
[ising-vitali]: https://github.com/phasetr/ising-model/blob/bb1a2dd19c8b70f33201daf130729ddb4790b66f/IsingModel/ComplexAnalyticity/VitaliPorter/Theorem.lean
[ising-montel]: https://github.com/phasetr/ising-model/blob/bb1a2dd19c8b70f33201daf130729ddb4790b66f/IsingModel/ComplexAnalyticity/VitaliPorter/MontelExtraction.lean
[ray-log]: https://github.com/girving/ray/blob/753f7131cf96f4651294de4398368abf136c34de/Ray/Analytic/Log.lean
[ray-integral]: https://github.com/girving/ray/blob/753f7131cf96f4651294de4398368abf136c34de/Ray/Analytic/Integral.lean
[ray-uniform]: https://github.com/girving/ray/blob/753f7131cf96f4651294de4398368abf136c34de/Ray/Analytic/Uniform.lean
[curvint-covering]: https://github.com/vbeffara/Curvint/blob/00b0bf1cfa3106fa92329f5f52e449186db0c9d3/Curvint/Covering.lean
[curvint-primitive]: https://github.com/vbeffara/Curvint/blob/00b0bf1cfa3106fa92329f5f52e449186db0c9d3/Curvint/Primitive.lean
[pr-primitive]: https://github.com/leanprover-community/mathlib4/blob/45e14c014f205131cc0eceda934abe9061abd23a/Mathlib/Analysis/Complex/Primitive.lean
[zulip-complex]: https://leanprover-community.github.io/archive/stream/116395-maths/topic/Multivariate.20complex.20analysis.html
[zulip-hadamard]: https://leanprover-community.github.io/archive/stream/423402-PrimeNumberTheorem%2B/topic/Hadamard.20factorization.20-.20PR.20ideas.html
[zulip-laurent]: https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Cauchy%27s.20residue.20theorem.20on.20punctured.20disk.html
[zulip-argument]: https://leanprover-community.github.io/archive/stream/116395-maths/topic/Argument.20principle.html
[zulip-contours]: https://leanprover-community.github.io/archive/stream/116395-maths/topic/contour.20integrals.html
