# Cubic forms: Lean formalization (mid snapshot)

This source-only Lean development proves a **conditional** theorem: every
homogeneous cubic over the rationals in at least ten variables has a nonzero
rational zero. **Five explicit mathematical premises remain.** Independent
proof checks do not discharge those premises or establish an unconditional proof.

## Exact theorem and assumptions

The current theorem is
[`CubicTenVariables.Theorem11ReducedZetaInternalCurves.main`](formalization/CubicTenVariables/CubicTenVariables/Theorem11ReducedZetaInternalCurves.lean).
Its conclusion expands to

```lean
∀ (n : ℕ), 10 ≤ n → ∀ F : MvPolynomial (Fin n) ℚ,
  F.IsHomogeneous 3 →
  ∃ x : Fin n → ℚ, x ≠ 0 ∧ MvPolynomial.eval x F = 0
```

There is no nonsingularity, local-solubility or rank hypothesis. The zero
polynomial is included. The definitions are in
[Targets.lean](formalization/CubicTenVariables/CubicTenVariables/Targets.lean).
The theorem takes these five propositions as ordinary arguments:

| Input | Assumed content and source |
| --- | --- |
| [ProjectiveMicrolocalCertificate](formalization/CubicTenVariables/CubicTenVariables/Literature/ProjectiveMicrolocalCertificate.lean) | A geometric certificate controlling the required hyperplane cohomology. A composite consequence of Beilinson, Raskin–Smith and Hu–Yang, with classical purity, coefficient compatibility and finiteness. |
| [SmoothCubicWeil](formalization/CubicTenVariables/CubicTenVariables/Literature/SmoothCubicWeil.lean) | Numerical finite-field bounds for smooth cubic hypersurfaces in the specified small dimensions, from Deligne's Weil theorem and their Betti numbers. |
| [ProperHyperplaneWeightDichotomy](formalization/CubicTenVariables/CubicTenVariables/Literature/ProperHyperplaneWeightDichotomy.lean) | A weight/second-moment alternative on one arithmetic open, with constants chosen before the finite field and parameter. A composite consequence of proper constructibility, Weil II and Xu's dichotomy. |
| [AffinePlaneCurveWeil](formalization/CubicTenVariables/CubicTenVariables/Literature/AffinePlaneCurveWeil.lean) | Degree-uniform counts for geometrically integral affine plane curves, including singular curves, in arbitrary degrees. Aubry–Perret's projective bound and the points at infinity give this form. |
| [CubicSurfaceZetaFactorBounds](formalization/CubicTenVariables/CubicTenVariables/Literature/CubicSurfaceZetaFactors.lean) | Fixed signed complex root families computing actual point counts of geometrically integral projective cubic surfaces in characteristic other than 2 or 3 over **every** finite extension, with low-weight and total-multiplicity bounds. The cohomological-degree-three root bound is not assumed. |

Their full quantifiers and hypotheses are in the linked Lean definitions.
The first and third are derived interfaces, **not five verbatim textbook
theorems**. AI-assisted mathematical source review found defensible derivations, including
the common arithmetic open and coefficient-compatible Gysin map, but those
derivations are not implemented in Lean. Detailed reference qualifications are
in [checks/mathematical-scope.md](checks/mathematical-scope.md).

An audit reporting only `propext`, `Classical.choice` and `Quot.sound` does not
make this theorem unconditional: mathematical hypotheses passed as arguments
are not Lean axioms.

## Internal counting results

The Pila and Heath-Brown counting premises formerly used on this route have
been removed. These are the precise consequences proved, not claims to have
formalized their full published theorems:

- [Primitive ternary count](formalization/TranslatedDepthSeven/TranslatedDepthSeven/PrimitiveProjectiveCurveAllChartsCountInternal.lean): for each fixed integer-coefficient homogeneous ternary form that is irreducible over the rationals and has degree at least two, the gcd-one integer zeros in the closed cube |xᵢ| ≤ B number O(B), counting both signs, for integer B ≥ 1. Constants may depend on the fixed form.
- [Bounded-degree curve count](formalization/TranslatedDepthSeven/TranslatedDepthSeven/BoundedDegreeRationalProjectiveCurveCountInternal.lean): for every N > 1, D and ε > 0, actual affine integer points (1,z) on rational homogeneous prime curves of degrees 2 through D number at most C_(N,D,ε) H^(1/2+ε), for real H ≥ 1, uniformly over their coefficients. This is not a bound for unrestricted rational projective points. The [centered residue-packet consequence](formalization/CubicTenVariables/CubicTenVariables/FixedLeadingSurfaceCenteredCurveCountInternal.lean) is also internal.
- [Cubic-surface amplification](formalization/CubicTenVariables/CubicTenVariables/CubicSurfaceAmplificationFromZeta.lean): the displayed zeta data, together with the proved estimate after adjoining a singular point, imply the required O(q) projective point-count error. Repeated roots and positive multiplicities are allowed; genuine finite-extension towers are used.

The [fixed-leading surface bound](formalization/CubicTenVariables/CubicTenVariables/FixedLeadingSurfaceNormalizedRegularCountInternalCurves.lean)
now uses only `AffinePlaneCurveWeil`: for every ε > 0 and each fixed absolutely irreducible
homogeneous ternary leading form k of degree at least four, integer zeros in
the closed box |xᵢ| ≤ B of every integer-coefficient ternary polynomial whose
highest-degree part is a nonzero rational multiple of k
number at most C_(k,ε) B^(1+ε). The constant precedes all lower coefficients and
real B ≥ 1. Decomposition, coverage, line directions and both curve-degree
ranges are internal. The general Salberger theorem is not claimed to have been
proved unconditionally.

## Verification performed

The publication copy was checked on macOS: all 2,152 selected local modules
were compiled from source without copying the research workspace's local
proof objects. All 12 external Git dependencies matched their manifest
commits and had no tracked changes; their compiled caches were reused.
The bounded build, independent final source rehash, publication audit, and
the shipped independent-checker script all passed. The latter replay used
the newly built publication objects.

| Check | Result and exact scope |
| --- | --- |
| Lean 4.26.0 build | Fresh compilation of the selected local proof sources; pinned external dependency caches reused. |
| Recursive publication axiom audit | Checks imported project theorem and definition bodies, including private declarations, and rejects project axioms or dependencies outside `propext`, `Classical.choice`, `Quot.sound`. |
| Literal main signature | The publication audit checks the actual five-input theorem directly against the expanded rational-zero statement above. |
| **Nanoda** | Independent Rust type checker checked **104,078 declarations** in the final main theorem's exported environment. |
| **Comparator** | Fresh Lean **4.35.0-rc3** kernel replay and expanded statement/definition comparison passed for that main, using a separately elaborated literal challenge. |
| Adversarial controls | Admitted proofs, a proved theorem of the wrong type, an altered definition behind an unchanged theorem alias, an ill-typed proof term and a forged `propext` type were rejected by the relevant checkers. Small isolated tests also rejected corrupted recursor rules, undeclared universe parameters and negative inductive occurrences. Canonical core-axiom comparison passed. |
| Source and artifact integrity | Source/object hashes, pinned checker versions, dependency commits, admission scan and archive contents checked. |
| Mathematical source review | AI-assisted review of actual point sets, substitutions, primitive vectors, projective charts, degree restrictions, constant ordering, coverage, extension towers, bad-prime local positivity and the five literature interfaces. The [local data](formalization/CubicTenVariables/CubicTenVariables/LocalizedSeriesUnconditional.lean#L26) are internally constructed at every prime, including 2 and 3; the [density argument](formalization/CubicTenVariables/CubicTenVariables/LocalZeroLowerBound.lean#L26) requires a derivative nonzero in ℚₚ, not a unit modulo p. No counterexample or invalid deduction was found in the reviewed paths. |

A broader same-kernel `lean4checker --fresh` replay of the entire imported
environment was stopped after about 26 minutes because of memory pressure.
It is **not credited as a completed check**. The completed Comparator replay
uses a fresh newer Lean kernel on the actual main proof closure; Nanoda checks
that closure in an independent Rust implementation.

These checks address different failure modes. They do **not** guarantee the
absence of kernel, exporter or checker bugs. The full exported environment of
the main theorem was independently replayed; this is not a claim that every
unrelated declaration in every public root received Nanoda/Comparator replay.
The source review is not a line-by-line mathematical review of every source file
or an independent human sign-off.
Incorrect informal interpretations or errors in unproved premises remain
possible. See [checks/checker-receipt.json](checks/checker-receipt.json) for
pins and control outcomes, and [checks/publication-receipt.json](checks/publication-receipt.json)
for the build and packaging receipt.

## Reproduce

Install Git and [Lean through elan](https://lean-lang.org/install/), clone this
repository, and run:

```sh
cd formalization/CubicTenVariables
lake exe cache get
cd ../..
./scripts/check.sh
```

The cache command downloads external dependencies' compiled artifacts. Keep
the three package directories together: their dependencies use relative paths.
Lean is pinned to **4.26.0**. The Lake manifests pin Mathlib to
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` and PrimeNumberTheoremAnd to
`db0b69d008f3991b6f03bc5f59504f02eb6c724b`, with their dependencies.
Do not run `lake update` when reproducing this snapshot. The external PNT
development has unrelated admissions; the publication audit rejects their use
in the selected project theorems.

GitHub Actions runs the build and publication audit on Linux after pushes and
pull requests. CI uses Ubuntu 24.04 with at most three concurrent module
compilations; local checks default to two. The local receipt describes macOS
checks; a future CI run is not counted as an already completed check. Optional
independent-checker reproduction is provided separately in
[scripts/independent-checks.sh](scripts/independent-checks.sh).

## Scope and provenance

This snapshot contains 2,150 original local Lean modules in the main theorem's
transitive import closure, package roots, and a publication audit. Historical
reductions may retain more assumptions; the five-input main above determines
the current claim. Some source comments describe intermediate work.
Manuscripts, drafts, progress notes, large exports, downloaded dependencies,
compiler caches, binaries and model files are excluded. Verification receipts
and scripts are included so that the published checks can be assessed.

Development used AI assistance in an interactive mathematical research workflow.
Reused code retains its attribution and license notices. Original project code
is licensed under Apache-2.0; see [LICENSE](LICENSE), [NOTICE](NOTICE) and
[CITATION.cff](CITATION.cff).
