import TranslatedDepthSeven.CurveNormalizationResidueDisc
import TranslatedDepthSeven.AuxiliaryFormFromEvaluationRank
import TranslatedDepthSeven.ColumnwiseDeterminantBound
import TranslatedDepthSeven.ProjectiveCurveSalbergerConstant

/-!
# Salberger's local curve-packet estimate

This file formalizes the determinant, auxiliary-form, and Bezout part of
Salberger 2023, Lemma 3.13, equation (3.14).  For a block of `s` independent
degree-`δ` forms and `s = δ(δ+3)/2`, one smooth one-parameter residue
disc supplies divisibility by `p^(0+⋯+(s-1))`.  Once this divisor is larger
than the archimedean determinant bound, every maximal minor vanishes, an
auxiliary degree-`δ` form exists, and projective Bezout gives at most `δ²`
points.

The only geometric data not constructed here are (i) the standard
degree-`δ` monomial block in the curve coordinate ring and (ii) the actual
formally-étale chart at the chosen nonsingular special-fiber point.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u w

/-- Number of degree-`δ` monomials used in Salberger's plane-projection
block. -/
def salbergerCurveMonomialCount (δ : ℕ) : ℕ :=
  δ * (δ + 3) / 2

/-- The exact concrete properties of Salberger's selected degree-`δ`
monomial block.  The final clause is the pointwise box bound supplied by
literal coefficient-one monomials. -/
def SalbergerCurveDegreeMonomialBlock
    {N δ : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (F : Fin (salbergerCurveMonomialCount δ) →
      MvPolynomial (Fin (N + 1)) ℤ) : Prop :=
  LinearIndependent ℚ (fun i ↦ Ideal.Quotient.mk I
      (MvPolynomial.map (Int.castRingHom ℚ) (F i))) ∧
  (∀ i, (F i).IsHomogeneous δ) ∧
  ∀ (V : ℕ) (x : Fin (N + 1) → ℤ),
    (∀ j, (x j).natAbs ≤ V) →
    ∀ i, (MvPolynomial.eval x (F i)).natAbs ≤ V ^ δ

namespace StandardAG

/-- The monomial-selection step in Salberger 2023, Lemma 3.13.  A birational
linear projection to an integral plane curve of degree `δ` gives
`δ(δ+3)/2` ambient degree-`δ` monomials independent in the curve
coordinate ring.  Their coefficient-one monomial form gives the displayed
box bound.

This is the degree-`δ` Hilbert-function statement for an integral
projective curve, obtainable from the standard generic-projection theorem
and the principal degree-`δ` ideal of its plane image. -/
def RationalProjectiveCurveDegreeMonomialBlock : Prop :=
  ∀ (N δ : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    I.IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    HasProjectiveDimensionDegree I 1 δ →
    ∃ F : Fin (salbergerCurveMonomialCount δ) →
        MvPolynomial (Fin (N + 1)) ℤ,
      SalbergerCurveDegreeMonomialBlock I F

end StandardAG

private theorem eval_map_intCast_eq
    (σ : Type u) (x : σ → ℤ) (P : MvPolynomial σ ℤ) :
    MvPolynomial.eval (fun i ↦ (x i : ℚ))
        (MvPolynomial.map (Int.castRingHom ℚ) P) =
      (MvPolynomial.eval x P : ℚ) := by
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp (Int.castRingHom ℚ) x P).symm

/-- Independent homogeneous forms on one actual smooth curve residue disc
admit a proper auxiliary form when the local divisor exceeds the explicit
columnwise determinant bound. -/
theorem exists_curvePacket_auxiliary_of_residue_disc
    {σ : Type u} {s S δ p : ℕ}
    (I : Ideal (MvPolynomial σ ℚ))
    (F : Fin s → MvPolynomial σ ℤ)
    (hF : LinearIndependent ℚ (fun i ↦ Ideal.Quotient.mk I
      (MvPolynomial.map (Int.castRingHom ℚ) (F i))))
    (hhom : ∀ i, (F i).IsHomogeneous δ)
    (x : Fin S → σ → ℤ)
    (hpositive : 0 < affineLineJetWeight s)
    (disc : CurveNormalizationResidueDisc.{u,0,w} σ (Fin S) p
      (affineLineJetWeight s) hpositive x)
    (C : Fin s → ℕ)
    (hbound : ∀ j i, (MvPolynomial.eval (x j) (F i)).natAbs ≤ C i)
    (hlarge : s.factorial * ∏ i, C i <
      p ^ affineLineJetWeight s) :
    ∃ G : MvPolynomial σ ℚ,
      G.IsHomogeneous δ ∧ G ∉ I ∧
        ∀ j : Fin S, MvPolynomial.eval (fun i ↦ (x j i : ℚ)) G = 0 := by
  classical
  apply exists_auxiliaryHomogeneousPolynomial_of_all_evaluation_minors_eq_zero
    I (fun i ↦ MvPolynomial.map (Int.castRingHom ℚ) (F i))
      (fun j i ↦ (x j i : ℚ)) hF (fun i ↦ (hhom i).map _)
  intro cols _hcols
  let V : Matrix (Fin s) (Fin s) ℤ :=
    Matrix.of (fun i j ↦ MvPolynomial.eval (x (cols j)) (F i))
  have hdiv : (p : ℤ) ^ affineLineJetWeight s ∣ V.det := by
    have hpositive' : 0 < affineLineJetWeight (Fintype.card (Fin s)) := by
      simpa only [Fintype.card_fin] using hpositive
    let selectedDisc : CurveNormalizationResidueDisc.{u,0,w}
        σ (Fin s) p (affineLineJetWeight (Fintype.card (Fin s)))
          hpositive' (fun j ↦ x (cols j)) := by
      simpa only [Fintype.card_fin] using disc.reindex cols
    have hlocal := CurveNormalizationResidueDisc.det_dvd
      (σ := σ) (ι := Fin s) hpositive' p (fun j ↦ x (cols j))
        selectedDisc F
    simpa only [Fintype.card_fin] using hlocal
  have hdetBound : V.det.natAbs ≤ s.factorial * ∏ i, C i := by
    have hboundT := det_natAbs_le_factorial_mul_prod_column_bounds
      V.transpose C (fun i j ↦ hbound (cols i) j)
    simpa only [Matrix.det_transpose, Fintype.card_fin] using hboundT
  have hpAbs : ((p : ℤ) ^ affineLineJetWeight s).natAbs =
      p ^ affineLineJetWeight s := by simp
  have hzero : V.det = 0 := by
    apply TangentMinors.eq_zero_of_dvd_of_natAbs_lt hdiv
    rw [hpAbs]
    exact hdetBound.trans_lt hlarge
  have heq :
      (Matrix.of (fun i j ↦
        MvPolynomial.eval (fun a ↦ (x j a : ℚ))
          (MvPolynomial.map (Int.castRingHom ℚ) (F i)))).submatrix id cols =
        (Int.castRingHom ℚ).mapMatrix V := by
    ext i j
    exact eval_map_intCast_eq σ (x (cols j)) (F i)
  rw [heq, ← RingHom.map_det, hzero, map_zero]

/-- Equation (3.14), with Salberger's determinant-size inequality displayed
literally.  Everything after the standard monomial block and the actual
smooth residue-disc chart is proved here. -/
theorem card_curvePacket_le_degree_sq_of_residue_disc
    (hMonomial : StandardAG.RationalProjectiveCurveDegreeMonomialBlock)
    (hBezout : StandardAG.RationalProjectiveCurveAuxiliaryFirstChartBezout)
    {N δ p V : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIdegree : HasProjectiveDimensionDegree I 1 δ)
    (points : Finset (IntVector N))
    (hIzero : ∀ z ∈ points, ∀ f ∈ I,
      MvPolynomial.eval (rationalIntegralAffineChartPoint z) f = 0)
    (hbox : ∀ z ∈ points, ∀ i,
      (integralAffineChartVector z i).natAbs ≤ V)
    (hpositive : 0 <
      affineLineJetWeight (salbergerCurveMonomialCount δ))
    (disc : CurveNormalizationResidueDisc.{0,0,w}
      (Fin (N + 1)) (Fin points.card) p
      (affineLineJetWeight (salbergerCurveMonomialCount δ)) hpositive
      (fun j ↦ integralAffineChartVector (points.equivFin.symm j).1))
    (hlarge : (salbergerCurveMonomialCount δ).factorial *
      V ^ (δ * salbergerCurveMonomialCount δ) <
        p ^ affineLineJetWeight (salbergerCurveMonomialCount δ)) :
    points.card ≤ δ ^ 2 := by
  classical
  obtain ⟨F, hF, hhom, hheight⟩ :=
    hMonomial N δ I hIprime hIhomogeneous hIdegree
  let x : Fin points.card → Fin (N + 1) → ℤ :=
    fun j ↦ integralAffineChartVector (points.equivFin.symm j).1
  have hbound : ∀ j i,
      (MvPolynomial.eval (x j) (F i)).natAbs ≤ V ^ δ := by
    intro j i
    apply hheight V (x j)
    intro a
    exact hbox (points.equivFin.symm j).1
      (points.equivFin.symm j).2 a
  have hlarge' : (salbergerCurveMonomialCount δ).factorial *
      ∏ _i : Fin (salbergerCurveMonomialCount δ), V ^ δ <
        p ^ affineLineJetWeight (salbergerCurveMonomialCount δ) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul] using hlarge
  obtain ⟨G, hGhom, hGnot, hGzeroFin⟩ :=
    exists_curvePacket_auxiliary_of_residue_disc
      I F hF hhom x hpositive disc (fun _ ↦ V ^ δ) hbound hlarge'
  have hGzero : ∀ z ∈ points,
      MvPolynomial.eval (rationalIntegralAffineChartPoint z) G = 0 := by
    intro z hz
    let j : Fin points.card := points.equivFin ⟨z, hz⟩
    have hj := hGzeroFin j
    have hx : x j = integralAffineChartVector z := by
      dsimp only [x, j]
      rw [Equiv.symm_apply_apply]
    simpa only [rationalIntegralAffineChartPoint, hx] using hj
  have hcard := card_integralAffinePoints_on_projectiveCurve_auxiliary_le
    hBezout I G hIprime hIhomogeneous hIdegree hGhom hGnot points
      hIzero hGzero
  simpa [pow_two] using hcard

end

end TranslatedDepthSeven
