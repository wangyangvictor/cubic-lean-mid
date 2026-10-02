# Mathematical scope of the five inputs

The checked theorem is an implication from five explicit propositions to
the stated rational-zero theorem. These propositions remain unproved Lean
arguments. The first and third below are composite derived interfaces,
not statements quoted verbatim from one theorem. The discussion records
a bounded AI-assisted source review of their intended derivations and uses; it is not
formal verification of the inputs or a guarantee against mathematical error.

1. **`ProjectiveMicrolocalCertificate`.** The same integral incidence equations
   must supply both the characteristic-zero conormal geometry and the
   finite-field trace cancellation. Separate existence assertions would
   not suffice. [Beilinson, §§1.3, 1.6.2 and 4.1](https://arxiv.org/pdf/1505.06768v8)
   supplies the support geometry; [Hu–Yang, Theorems 5.8–5.9](https://arxiv.org/pdf/1702.06752v1)
   supplies one arithmetic localization for the finite-coefficient support.

   A necessary additional comparison concerns the **actual Gysin map**.
   For the ambient hyperplane immersion, tensoring its divisor class with
   the pushed-forward constant sheaf gives the purity/counit composite:
   [Saito, §7.1, (7.8), (7.13), Lemma 7.3(3)](https://arxiv.org/pdf/1510.03018v4).
   Kummer divisor classes commute with adjacent coefficient reductions,
   so these maps form a compatible tower. This uses a natural morphism,
   not an assertion that an arbitrary `i!` commutes with tensor product.

   The mod-ℓ microsupport controls every ℤ/ℓʳ level by coefficient filtration.
   Apply [Raskin–Smith, §2, especially Lemma 2.5](https://arxiv.org/html/2106.10332v1)
   at finite coefficients; Saito's Proposition 7.13 is field-only and should
   not itself be cited at all prime-power coefficient levels. Finite
   cohomology permits the inverse limit; [Milne, Theorem 19.2](https://www.jmilne.org/math/CourseNotes/LEC.pdf)
   supplies finite generation and the coefficient sequence. Fixed mod-ℓ
   constructibility bounds the adic ranks. The exceptional primes are
   selected once, not by taking a union over coefficient levels.

   With `dim X = n−2` and projective contact dimension at most `e−1`, the
   resulting range is exactly `k > n−1+e`. Reducible or nonreduced equations
   and hyperplanes containing components do not require purity for the
   potentially singular immersion `X ∩ H → X`. This finite-coefficient
   derivation was reviewed independently by two agents, but is not a Lean proof.

2. **`SmoothCubicWeil`.** [Deligne, Weil I, Theorem 8.1](https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf)
   gives the smooth projective estimate. For cubic hypersurfaces of dimensions
   1, 2 and 3, the primitive middle Betti numbers are 2, 6 and 10.
   The exact affine-cone identity then gives the interface's squared bound
   `100 (q−1)² q^r` for `(N_aff−q^(r+1))²`. Geometric smoothness is required;
   this input does not assert the same estimate for arbitrary singular cubics.

3. **`ProperHyperplaneWeightDichotomy`.** The trace is literally
   `1 + q #(X ∩ H_v) − #X`, including zero frequency. The proper incidence
   family and the constant family supply its virtual constant-coefficient
   complex. [Xu, Theorem 3.5 and Remark 3.6](https://arxiv.org/pdf/1709.01663)
   supplies the alternative on a smooth finite-field base, including mixed
   lisse sheaves. It does not alone supply the interface's common arithmetic open.

   For that step, use proper adic constructibility. Pass from each relevant
   cohomology λ-module to its quotient by bounded ℓ-power torsion; this
   preserves its rationalization. This does not assert that shrinking the
   base kills generic torsion. Choose flat adic representatives of these
   torsion-free quotients:
   [Laszlo–Olsson II, §8 and proof of Theorem 3.9(4)–(5)](https://www.cmls.polytechnique.fr/perso/laszlo/articleweb/article-IIfin.pdf).
   Choose one open where all their mod-ℓ levels are lisse. The short exact
   coefficient sequences and closure under extensions make every level of
   these representatives lisse on that same open. Shrink for smooth geometrically
   integral fibres of the specified dimension ([Stacks 0559](https://stacks.math.columbia.edu/tag/0559)
   and the smooth locus). Weil II gives integer mixed weights on each fibre.
   Applying Xu there gives either the uniform low-weight bound or infinitely
   many normalized second moments at least `1/2`, with `g,N,C` fixed before
   `p,w,K`. No countable intersection of opens is taken. The broad `n=0` case
   is separate and trivial: the defect is `1`. This global argument remains
   outside Lean. Singular or reducible source fibres are allowed.

4. **`AffinePlaneCurveWeil`.** [Aubry–Perret, Corollary 2.5](https://www.math.univ-toulouse.fr/~perret/Fichiers/Scan-Weil.Singulier.pdf)
   gives the projective plane-curve bound, including singular geometrically
   integral curves. Removing at most degree-many points at infinity gives
   the degree-uniform affine bound in the interface. No rational-point
   assumption is needed; the constant precedes the field and coefficients.

5. **`CubicSurfaceZetaFactorBounds`.** For geometrically integral projective
   cubic surfaces in characteristic other than 2 or 3, the trace formula gives
   fixed complex root families computing counts over every finite extension, with the
   cohomological signs `−,+,−` and repeated roots counted with positive
   multiplicity. [GeometricallyIntegralForm](../formalization/CubicTenVariables/CubicTenVariables/Literature/FiniteFieldPointCounts.lean#L65)
   explicitly includes `F ≠ 0`, so the zero polynomial is excluded.
   [Deligne, Weil II, Corollary 3.3.4](https://publications.ias.edu/sites/default/files/Number40.pdf)
   supplies the required low-weight bounds. [Katz, BettiSum, corollary to
   Theorem 3](https://web.math.princeton.edu/~nmk/BettiSum14.pdf) gives total
   Betti number at most `23328`; removing the one-dimensional `H⁰` and `H⁴`
   gives `23326`. The high-degree root bound is not assumed. The internal
   amplification uses genuine finite-extension towers and positive
   multiplicities, and its geometric estimate retains nonconicality.

No counterexample or invalid deduction was found in these reviewed paths.
The review was not a line-by-line mathematical audit of every public file.
Kernel and independent-checker success verifies the formal implication;
it does not discharge these inputs or validate every informal interpretation.

## Historical source comments

`HomogeneousProjectionCountingBridge` calls its fibre bound “scheme-theoretic”, but the literal definition bounds distinct geometric points, which is what the counting proof uses.
The comment beside `AffinePlaneCubicWeil` describes a cubic specialization; the published final main still takes the all-degree `AffinePlaneCurveWeil` input.
The “still-open” wording in `FixedLeadingFormGoodSurfaceCountReduction` is historical: later modules supply that surface statement along the current five-input route.
