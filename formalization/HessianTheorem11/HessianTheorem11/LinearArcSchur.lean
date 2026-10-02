import HessianTheorem11.FormalSmoothArc
import HessianTheorem11.PolynomialSchurVanishing
import HessianTheorem11.SchurSecondOrder
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Quadratic Schur coefficients along actual arcs in arbitrary affine
varieties. The only geometric input is universal smooth-arc lifting. -/
noncomputable section
namespace HessianTheorem11.LinearArcSchur
open MvPolynomial Matrix Module SchurSecondOrder PolynomialSchurVanishing
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

variable {n : ℕ} {α κ : Type*} [Fintype α] [Fintype κ] [DecidableEq κ]

theorem schur_eq_zero_of_vanishing_ideal
    {R : Type*} [CommRing R]
    (Z : Set (GeometricPoint n))
    (A : Matrix α α (GeometricPolynomial n)) (C : Matrix α κ (GeometricPolynomial n))
    (D : Matrix κ α (GeometricPolynomial n)) (G : Matrix κ κ (GeometricPolynomial n))
    (hrank : ∀ y ∈ Z, ((fromBlocks A C D G).map (eval y)).rank ≤ Fintype.card κ)
    (φ : GeometricPolynomial n →+* R)
    (hφ : ∀ P ∈ vanishingIdeal GeometricField Z, φ P = 0)
    (J : Matrix κ κ R) (hGJ : G.map φ * J = 1) :
    A.map φ - C.map φ * J * D.map φ = 0 := by
  have hz (i j : α) : φ (bordered A C D G i j).det = 0 := by
    apply hφ
    intro y hy
    change eval y _ = 0
    rw [RingHom.map_det, bordered_eq_submatrix]
    apply det_eq_zero_of_rank_lt
    have h := (PolynomialSchurVanishing.rank_submatrix_le
      ((fromBlocks A C D G).map (eval y))
      (Sum.elim (fun _ : Fin 1 => Sum.inl i) Sum.inr)
      (Sum.elim (fun _ : Fin 1 => Sum.inl j) Sum.inr)).trans (hrank y hy)
    simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_comm] using
      Nat.lt_of_le_of_lt h (Nat.lt_add_one (Fintype.card κ))
  ext i j
  have h := hz i j
  rw [RingHom.map_det] at h
  change ((bordered A C D G i j).map φ).det = 0 at h
  rw [bordered_map, det_bordered _ _ _ _ J hGJ i j] at h
  apply (Matrix.isUnit_det_of_right_inverse hGJ).mul_left_cancel
  simpa only [Matrix.zero_apply, mul_zero] using h

def matrixPolynomial {ι τ : Type*}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix ι τ GeometricField) :
    Matrix ι τ (GeometricPolynomial n) :=
  fun a b => ∑ i, C (M (Pi.single i 1) a b) * X i

theorem linear_coordinate_expansion {W : Type*} [AddCommGroup W]
    [Module GeometricField W] (M : GeometricPoint n →ₗ[GeometricField] W)
    (x : GeometricPoint n) : M x = ∑ i, x i • M (Pi.single i 1) := by
  have hx : x = ∑ i, x i • (Pi.single i (1 : GeometricField) : GeometricPoint n) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  simp only [map_smul]

theorem eval_matrixPolynomial {ι τ : Type*}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix ι τ GeometricField)
    (x : GeometricPoint n) : (matrixPolynomial M).map (eval x) = M x := by
  rw [linear_coordinate_expansion M x]
  ext a b
  simp [matrixPolynomial, mul_comm, Matrix.sum_apply]

theorem coefficient_matrixPolynomial {ι τ : Type*}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix ι τ GeometricField)
    (γ : Fin n → PowerSeries GeometricField) (d : ℕ) :
    matrixCoeff d ((matrixPolynomial M).map (arcEval γ)) = M (arcCoefficient γ d) := by
  rw [linear_coordinate_expansion M (arcCoefficient γ d)]
  ext a b
  simp [matrixPolynomial, matrixCoeff, arcEval, PowerSeries.coeff_C_mul,
    arcCoefficient, mul_comm, Matrix.sum_apply]

theorem matrixSeries_isUnit_det (G : Matrix κ κ (PowerSeries GeometricField))
    (hG : (matrixCoeff 0 G).det ≠ 0) : IsUnit G.det := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [RingHom.map_det]
  have he : PowerSeries.constantCoeff.mapMatrix G = matrixCoeff 0 G := by
    ext i j
    exact (congrFun PowerSeries.coeff_zero_eq_constantCoeff (G i j)).symm
  rw [he]
  exact isUnit_iff_ne_zero.mpr hG

/-- For every tangent direction, the quadratic Schur product lies in the
range of the actual linear upper-left block. Higher arc coefficients and
all varying complementary blocks remain in the power-series calculation. -/
theorem quadratic_schur_lift (SA : FormalSmoothArcInput)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z =
      (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (A : GeometricPoint n →ₗ[GeometricField] Matrix α α GeometricField)
    (C : GeometricPoint n →ₗ[GeometricField] Matrix α κ GeometricField)
    (G : GeometricPoint n →ₗ[GeometricField] Matrix κ κ GeometricField)
    (hrank : ∀ y ∈ Z, (fromBlocks (A y) (C y) (C y).transpose (G y)).rank ≤ Fintype.card κ)
    (hC : C x = 0) (hG : (G x).det ≠ 0)
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x) :
    ∃ w : GeometricPoint n, A w = C v * (G x)⁻¹ * (C v).transpose := by
  classical
  obtain ⟨γ,hγ0,hγ1,hγ⟩ := SA.lift Z hZ hirred x hx hdim v hv
  let Ap := matrixPolynomial A
  let Cp := matrixPolynomial C
  let Gp := matrixPolynomial G
  let φ := arcEval γ
  have hg0 : matrixCoeff 0 (Gp.map φ) = G x := by
    simpa only [Gp,φ,coefficient_matrixPolynomial,hγ0]
  have hgu : IsUnit (Gp.map φ).det := matrixSeries_isUnit_det _ (by rwa [hg0])
  let J := (Gp.map φ)⁻¹
  have hGJ : Gp.map φ * J = 1 := Matrix.mul_nonsing_inv _ hgu
  have hs : Ap.map φ - Cp.map φ * J * (Cp.map φ).transpose = 0 := by
    apply schur_eq_zero_of_vanishing_ideal Z Ap Cp Cp.transpose Gp _ φ hγ J hGJ
    intro y hy
    simpa only [Ap,Cp,Gp,Matrix.fromBlocks_map,Matrix.transpose_map,
      eval_matrixPolynomial] using hrank y hy
  have hc0 : matrixCoeff 0 (Cp.map φ) = 0 := by
    simpa only [Cp,φ,coefficient_matrixPolynomial,hγ0] using hC
  letI : Invertible (matrixCoeff 0 (Gp.map φ)) :=
    Matrix.invertibleOfIsUnitDet _ (by rw [hg0]; exact isUnit_iff_ne_zero.mpr hG)
  have he := schur_second_identity (Ap.map φ) (Cp.map φ) (Gp.map φ) J hGJ hc0 hs
  refine ⟨arcCoefficient γ 2,?_⟩
  have hi : ⅟(matrixCoeff 0 (Gp.map φ)) = (G x)⁻¹ := by
    rw [Matrix.invOf_eq_nonsing_inv, hg0]
  simpa only [Ap,Cp,φ,coefficient_matrixPolynomial,hγ1,hi] using he

/-- Polarizing three actual one-parameter lifts gives the mixed
tangent coefficient, without introducing multivariable formal parameters. -/
theorem mixed_schur_mem_range (SA : FormalSmoothArcInput)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z =
      (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (A : GeometricPoint n →ₗ[GeometricField] Matrix α α GeometricField)
    (C : GeometricPoint n →ₗ[GeometricField] Matrix α κ GeometricField)
    (G : GeometricPoint n →ₗ[GeometricField] Matrix κ κ GeometricField)
    (hrank : ∀ y ∈ Z, (fromBlocks (A y) (C y) (C y).transpose (G y)).rank ≤ Fintype.card κ)
    (hC : C x = 0) (hG : (G x).det ≠ 0)
    (a b : GeometricPoint n) (ha : a ∈ affineTangentSpace Z x)
    (hb : b ∈ affineTangentSpace Z x) :
    C a * (G x)⁻¹ * (C b).transpose + C b * (G x)⁻¹ * (C a).transpose ∈
      LinearMap.range A := by
  obtain ⟨w,hw⟩ := quadratic_schur_lift SA Z hZ hirred x hx hdim A C G
    hrank hC hG (a+b) ((affineTangentSpace Z x).add_mem ha hb)
  obtain ⟨u,hu⟩ := quadratic_schur_lift SA Z hZ hirred x hx hdim A C G hrank hC hG a ha
  obtain ⟨v,hv⟩ := quadratic_schur_lift SA Z hZ hirred x hx hdim A C G hrank hC hG b hb
  refine ⟨w-u-v,?_⟩
  rw [map_sub,map_sub,hw,hu,hv,map_add,Matrix.transpose_add,
    Matrix.add_mul,Matrix.add_mul,Matrix.mul_add,Matrix.mul_add]
  abel

end HessianTheorem11.LinearArcSchur
