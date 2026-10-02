import CubicTenVariables.Literature.PolynomialExponentialDichotomy
import CubicTenVariables.PrimeSumAdapter

/-!
A narrower UNPROVED literature interface for the only polynomial-exponential
family used in the small-degree-cone argument. Its trace is the literal
projective hyperplane point-count defect, with no additive character or
arbitrary phase. No axiom and no unconditional inhabitant is declared.

Geometric construction: over the actual integral parameter base, use the
proper incidence family I -> S and the constant family X_F -> S. The virtual
complex Q_l + R pi_* Q_l(-1) - R p_* Q_l has the displayed trace. A common
dense principal open is chosen by adic constructibility before any good
prime is chosen; proper base change identifies all finite-field fibers.
The constant coefficients eliminate Artin--Schreier systems from this route.
They do not eliminate the mixed virtual trace-function weight alternative.

Precise primary references for the remaining arithmetic argument are Xu,
arXiv:1709.01663v1, Theorem 3.5, Remark 3.6 and its mixed extension on printed
pp.19--20; the proof on pp.20--22 treats cancellation of arithmetic simple
constituents. Global adaptation can also be obtained from Fouvry--Katz,
J. reine angew. Math. 540 (2001), Theorem 2.1, with zero phase and constant
coefficients on these proper families. Its printed rank bound needs the
factor C corrected by Bonolis--Kowalski--Woo, author version 21 May 2026,
Remark 5.2(1). Apply the theorem to the already restricted base, not by
closed base change of a stratification of ambient affine space. Remove
finitely many primes so the chosen open has smooth geometrically integral
fibers of dimension d (Stacks Tag 0559 and the smooth locus).

The formal theorem `of_polynomial` below proves only that the existing,
broader literature premise implies this one; it does NOT discharge either
premise. The finite-sum identities used in that implication are proved.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.ProperHyperplaneFamily
open MvPolynomial PolynomialExponentialFamily ProjectiveFourierIdentity
open scoped BigOperators Classical

/-- Literal point-count defect of a projective hypersurface and its actual
hyperplane section. At zero frequency the section is the entire hypersurface. -/
def defect {n : ℕ} (F : ParameterPolynomial n)
    (K : Type*) [Field K] [Fintype K] (v : Fin n → K) : ℂ :=
  1 + (Fintype.card K : ℂ) *
    (Nat.card (sectionPoints (map (Int.castRingHom K) F) v) : ℂ) -
    (Nat.card (zeroPoints (map (Int.castRingHom K) F)) : ℂ)

/-- The exact cone Fourier identity, valid also at the zero frequency.
This uses no cohomology or literature input. -/
theorem fiberSum_eq_defect {n e : ℕ} (F : ParameterPolynomial n)
    (hF : F.IsHomogeneous e) (he : 0 < e)
    {K : Type*} [Field K] [Fintype K] (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (v : Fin n → K) :
    fiberSum (hypersurface F) (fourierPhase n) ψ v = defect F K v := by
  rw [fiberSum_hypersurface]
  simpa only [FiniteFieldFourier.zeroFiberSum, Finset.sum_filter, defect] using
    zeroFiberSum_eq_projective_counts ψ hψ (map (Int.castRingHom K) F)
      (hF.map _) he v

/-- The manuscript's normalized Fourier trace is the same literal defect
at nonzero frequency, for every nontrivial finite-field additive character. -/
theorem normalizedFourierSum_eq_defect {n e : ℕ} (F : ParameterPolynomial n)
    (hF : F.IsHomogeneous e) (he : 0 < e)
    {K : Type*} [Field K] [Fintype K] (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (v : Fin n → K) (hv : v ≠ 0) :
    normalizedFourierSum ψ (map (Int.castRingHom K) F) v = defect F K v :=
  normalizedFourierSum_eq_projective_counts ψ hψ
    (map (Int.castRingHom K) F) (hF.map _) he v hv

end CubicTenVariables.ProperHyperplaneFamily

namespace CubicTenVariables.Literature
open MvPolynomial Filter PolynomialExponentialFamily FiniteFieldTraceCharacter
open scoped BigOperators Topology Classical

/-- UNPROVED constant-coefficient proper-hyperplane-family weight alternative.
The same open, excluded-prime integer and rank bound precede p, K and w.
No estimate of a moment, cubic anisotropy or desired weight bound is assumed. -/
def ProperHyperplaneWeightDichotomy : Prop :=
  ∀ (n e t d : ℕ) (F : ParameterPolynomial n), F.IsHomogeneous e → 0 < e →
    ∀ (G : Fin t → ParameterPolynomial n) (h : ParameterPolynomial n),
    (baseIdeal G).IsPrime →
    ((baseIdeal G).map (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ baseIdeal G) = d →
    map (Int.castRingHom ℚ) h ∉ baseIdeal G →
    ∃ (g : ParameterPolynomial n) (N C : ℕ),
      map (Int.castRingHom ℚ) g ∉ baseIdeal G ∧ h ∣ g ∧ 1 ≤ N ∧ 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N → ∀ w : ℕ,
          (∀ (K : Type) [Field K] [Fintype K] [CharP K p]
            (v : Fin n → K), v ∈ parameterPoints G g K →
            ‖ProperHyperplaneFamily.defect F K v‖ ≤
              (C : ℝ) * (Fintype.card K : ℝ)^((w : ℝ)/2)) ∨
          (∃ᶠ a : ℕ in atTop, (1/2 : ℝ) ≤
            (∑ v ∈ parameterPoints G g (Extension p a),
              ‖ProperHyperplaneFamily.defect F (Extension p a) v‖^2) /
              (p : ℝ)^(a*(d+w+1)))

/-- This new premise is a proved weakening of the previous polynomial
exponential-family premise. The old premise remains an explicit argument. -/
theorem ProperHyperplaneWeightDichotomy.of_polynomial
    (dichotomy : PolynomialExponentialDichotomy) : ProperHyperplaneWeightDichotomy := by
  intro n e t d F hF he G h hprime hgeometric hdim hh
  obtain ⟨g, N, C, hg, hhg, hN, hC, halt⟩ := dichotomy n n t 1 d G
    (hypersurface F) (fourierPhase n) h hprime hgeometric hdim hh
  refine ⟨g, N, C, hg, hhg, hN, hC, ?_⟩
  intro p _ hpN w
  have hψ := PrimeSumAdapter.stdAddChar_ne_one p
  have hid (K : Type) [Field K] [Fintype K] [CharP K p] (v : Fin n → K) :
      fiberSum (hypersurface F) (fourierPhase n)
        (primeTraceCharacter p K ZMod.stdAddChar) v = ProperHyperplaneFamily.defect F K v :=
    ProperHyperplaneFamily.fiberSum_eq_defect F hF he _
      (primeTraceCharacter_ne_one p K ZMod.stdAddChar hψ) v
  rcases halt p hpN ZMod.stdAddChar hψ w with hbound | hlarge
  · left
    intro K _ _ _ v hv
    simpa only [hid] using hbound K v hv
  · right
    simpa only [hid] using hlarge

end CubicTenVariables.Literature
