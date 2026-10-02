import HessianTheorem11.UnconditionalResidueTarget
import HessianTheorem11.UnconditionalValuationRelativeLimit
import HessianTheorem11.UnconditionalWeightLimitDescent

/-! Geometric relative one-parameter degeneration, proved from actual
valuative specialization, Cartan diagonalization, finite character equations,
ordered-group elimination, and algebraically closed field existence. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace HessianTheorem11.UnconditionalGeometricRelativeLimit
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
  ReducedRelative ReducedWeightCurve UnconditionalAlgebraicExistence UnconditionalIntegralOrbit
  UnconditionalResidueTarget UnconditionalValuationRelative UnconditionalValuationWeights
  UnconditionalWeightLimitDescent UnconditionalOrbitIdeal

/-- If the actual orbit closure meets a closed invariant homogeneous
target avoiding F, an actual SL coordinate frame and nonzero integral
sum-zero weight have an admissible zero-weight limit in that target. -/
theorem exists_geometric_weight_limit {n d : ℕ} (hn : 0 < n)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous d)
    (S : Set (GeometricPolynomial n)) (hclosed : coefficientClosed S)
    (hinv : slInvariant S) (hhom : ∀ H ∈ S, H.IsHomogeneous d)
    (G : GeometricPolynomial n) (hG : G ∈ S) (hGF : G ∈ slOrbitClosure F)
    (hnot : F ∉ S) :
    ∃ (B : Matrix (Fin n) (Fin n) GeometricField) (w : Fin n → ℤ),
      B.det = 1 ∧ w ≠ 0 ∧ (∑ i, w i = 0) ∧
      HasNonnegativeWeights (restrict B F) w ∧ zeroWeightPart (restrict B F) w ∈ S := by
  classical
  obtain ⟨V,c,A,B,δ,P,hc,hA,hB,hBi,hδ,hprod,hP,hcenter,hdiag⟩ :=
    exists_integral_orbit_model hn F hF G hGF
  let κ := IsLocalRing.ResidueField V
  letI : Algebra GeometricField κ := ((IsLocalRing.residue V).comp c).toAlgebra
  have hcr : (IsLocalRing.residue V).comp c = algebraMap GeometricField κ := rfl
  letI : Infinite κ := Infinite.of_injective (algebraMap GeometricField κ)
    (algebraMap GeometricField κ).injective
  let C : MvPolynomial (Fin n) V := restrict A (map c F)
  let H : MvPolynomial (Fin n) V := restrict B⁻¹ P
  let T : Set (MvPolynomial (Fin n) κ) := extendedTarget d S
  have hC : C.IsHomogeneous d := homogeneous_restrict A (map c F) (hF.map c)
  have hTc : coefficientClosed T := extendedTarget_coefficientClosed d S
  have hTi : slInvariant T := extendedTarget_slInvariant d S hclosed hhom hinv
  have hTh : ∀ Q ∈ T, Q.IsHomogeneous d := fun Q hQ => hQ.1
  have hH : residuePolynomial V H ∈ T :=
    residue_target_mem V c hcr S hclosed hhom hinv G hG P hP hcenter B⁻¹ hBi
  have hCn : residuePolynomial V C ∉ T :=
    residue_source_notMem V c hcr F hF S hclosed hhom hinv hnot A hA
  obtain ⟨w,hwne,hw,hW,horder⟩ := integral_diagonal_relative_weight V hn C H hC δ hδ hprod
    hdiag T hTc hTi hTh hH hCn
  have hlim : zeroWeightPart (residuePolynomial V C) w ∈ T := by
    have hh := (relativeOrder_pos_iff (residuePolynomial V C)
      (hC.map (IsLocalRing.residue V)) T hTc hCn (identityWeightFrame w hw)).mp
      (by omega : 0 < relativeOrder d (residuePolynomial V C) T (identityWeightFrame w hw))
    rwa [originalCurve_identity,curve_zero _ _ hW] at hh
  let Abar : Matrix (Fin n) (Fin n) κ := A.map (IsLocalRing.residue V)
  have hAb : Abar.det = 1 := by
    exact ((IsLocalRing.residue V).map_det A).symm.trans (by rw [hA,map_one])
  have hCe : residuePolynomial V C =
      restrict Abar (map (algebraMap GeometricField κ) F) :=
    residue_restriction_map V c hcr A F
  have hWa : HasNonnegativeWeights (restrict Abar (map (algebraMap GeometricField κ) F)) w :=
    hCe ▸ hW
  have hTe : ∀ q : MvPolynomial (Fin n →₀ ℕ) GeometricField,
      coefficientVanishing S q → aeval (fun e => coeff e
        (zeroWeightPart (restrict Abar (map (algebraMap GeometricField κ) F)) w)) q = 0 := by
    intro q hq
    have he := extendedTarget_equations d S hhom (zeroWeightPart (residuePolynomial V C) w) hlim q hq
    rwa [hCe] at he
  obtain ⟨D,hD,hWD,hTD⟩ := exists_base_weight_limit F S hclosed w Abar hAb hWa hTe
  exact ⟨D,w,hD,hwne,hw,hWD,hTD⟩

/-- The geometric degeneration as an actual SL weight frame, with strictly
positive order of the original target's ideal along the original-coordinate
orbit curve. This is the existence endpoint needed by relative optimization. -/
theorem exists_geometric_relative_frame {n d : ℕ} (hn : 0 < n)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous d)
    (S : Set (GeometricPolynomial n)) (hclosed : coefficientClosed S)
    (hinv : slInvariant S) (hhom : ∀ H ∈ S, H.IsHomogeneous d)
    (G : GeometricPolynomial n) (hG : G ∈ S) (hGF : G ∈ slOrbitClosure F)
    (hnot : F ∉ S) :
    ∃ f : RationalDescent.WeightFrame GeometricField n,
      f.matrix.det = 1 ∧ f.weight ≠ 0 ∧
      HasNonnegativeWeights (restrict f.matrix F) f.weight ∧
      0 < relativeOrder d F S f := by
  obtain ⟨B,w,hB,hwne,hw,hW,hT⟩ :=
    exists_geometric_weight_limit hn F hF S hclosed hinv hhom G hG hGF hnot
  have hu : IsUnit B.det := hB ▸ isUnit_one
  let f : RationalDescent.WeightFrame GeometricField n :=
    { matrix := B
      injective := Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det B).mpr hu)
      weight := w
      sum_zero := hw }
  refine ⟨f,hB,hwne,hW,?_⟩
  apply (relativeOrder_pos_iff F hF S hclosed hnot f).mpr
  rw [originalCurve_zero F f hW]
  apply hinv B⁻¹ _ _ hT
  rw [Matrix.det_nonsing_inv,hB,Ring.inverse_one]

end HessianTheorem11.UnconditionalGeometricRelativeLimit
