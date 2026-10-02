import CubicTenVariables.FiniteFieldCubicOrder
import CubicTenVariables.FiniteMatrixActiveCoordinates
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Integral algebraic certificates for one cubic descent step.  A coordinate
change lifts a residue-field invertible matrix; exactly three coordinates
are then multiplied by p.  The transformed polynomial is divided by p
coefficientwise.  No existence of p-adic zeros or iteration is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PadicCubicDescent
open MvPolynomial HessianTheorem11 PolynomialRestriction PolynomialWeightTransport
open scoped BigOperators
variable {p n m : ℕ} [Fact p.Prime]

/-- Literal reduction vanishes exactly when p divides an integral coefficient. -/
theorem reduction_eq_zero_iff (a : ℤ_[p]) :
    PadicInt.toZMod a = 0 ↔ (p : ℤ_[p]) ∣ a := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

/-- A homogeneous polynomial whose reduction is zero has a homogeneous
integral quotient by the constant polynomial p. -/
theorem exists_homogeneous_quotient (F : MvPolynomial (Fin n) ℤ_[p])
    (hF : F.IsHomogeneous 3) (hred : map PadicInt.toZMod F = 0) :
    ∃ G : MvPolynomial (Fin n) ℤ_[p], G.IsHomogeneous 3 ∧ F = C (p : ℤ_[p]) * G := by
  obtain ⟨G,hG⟩ := (C_dvd_iff_map_hom_eq_zero PadicInt.toZMod (p : ℤ_[p])
    reduction_eq_zero_iff F).mpr hred
  refine ⟨G,?_,hG⟩
  intro d hd
  apply hF
  rw [hG,coeff_C_mul]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hd

/-- Entrywise lifts of an invertible residue matrix have determinant norm one. -/
theorem exists_matrix_lift (B : Matrix (Fin n) (Fin n) (ZMod p))
    (hB : B.det ≠ 0) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ_[p], U.map PadicInt.toZMod = B ∧ ‖U.det‖ = 1 := by
  classical
  have hs := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
  choose u hu using fun i j => hs (B i j)
  let U : Matrix (Fin n) (Fin n) ℤ_[p] := u
  have he : U.map PadicInt.toZMod = B := by ext i j; exact hu i j
  refine ⟨U,he,PadicInt.isUnit_iff.mp ?_⟩
  apply IsLocalRing.notMem_maximalIdeal.mp
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
  rw [RingHom.map_det]
  change (U.map PadicInt.toZMod).det ≠ 0
  rwa [he]

/-- Scaling precisely the coordinates in s. -/
def scaleMatrix (s : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℤ_[p] :=
  Matrix.diagonal (fun j => if j ∈ s then (p : ℤ_[p]) else 1)

theorem det_scaleMatrix (s : Finset (Fin n)) :
    (scaleMatrix (p := p) s).det = (p : ℤ_[p]) ^ s.card := by
  classical
  simp [scaleMatrix,Matrix.det_diagonal]

/-- The residue-field form becomes zero after the chosen directions are scaled. -/
theorem restrict_reduction_scale_eq_zero
    (A : Matrix (Fin m) (Fin n) (ZMod p))
    (B : Matrix (Fin n) (Fin n) (ZMod p)) (s : Finset (Fin n))
    (hAB : ∀ i j, j ∉ s → (A * B) i j = 0)
    (U : Matrix (Fin n) (Fin n) ℤ_[p]) (hU : U.map PadicInt.toZMod = B)
    (G : MvPolynomial (Fin m) (ZMod p)) (hG : G.IsHomogeneous 3) :
    restrict ((U * scaleMatrix (p := p) s).map PadicInt.toZMod)
      (restrict A G) = 0 := by
  classical
  rw [restrict_restrict]
  have hmat : A * (U * scaleMatrix (p := p) s).map PadicInt.toZMod = 0 := by
    rw [Matrix.map_mul,hU,← Matrix.mul_assoc]
    ext i j
    simp only [scaleMatrix,Matrix.zero_apply]
    by_cases hj : j ∈ s
    · simp [hj]
    · simp [hj,hAB i j hj]
  rw [hmat]
  have he : linearForms (0 : Matrix (Fin m) (Fin n) (ZMod p)) = 0 := by
    ext i; simp [linearForms]
  unfold restrict
  rw [he]
  have hc : coeff 0 G = 0 := hG.coeff_eq_zero (by simp)
  change eval₂ C (fun _ => 0) G = 0
  rw [eval₂_zero'_apply]
  simpa only [constantCoeff_eq,map_zero] using congrArg C hc

/-- Supplied finite-field coordinates give the literal integral descent
certificate; the active-coordinate set has exactly three elements. -/
theorem exists_step_of_coordinates
    (F : MvPolynomial (Fin n) ℤ_[p]) (hF : F.IsHomogeneous 3)
    (A : Matrix (Fin m) (Fin n) (ZMod p))
    (G₀ : MvPolynomial (Fin m) (ZMod p)) (hG₀ : G₀.IsHomogeneous 3)
    (hFG : map PadicInt.toZMod F = restrict A G₀)
    (B : Matrix (Fin n) (Fin n) (ZMod p)) (hB : B.det ≠ 0)
    (s : Finset (Fin n)) (hs : s.card = 3)
    (hAB : ∀ i j, j ∉ s → (A * B) i j = 0) :
    ∃ (T : Matrix (Fin n) (Fin n) ℤ_[p]) (G : MvPolynomial (Fin n) ℤ_[p]),
      G.IsHomogeneous 3 ∧ restrict T F = C (p : ℤ_[p]) * G ∧
      ‖T.det‖ = ‖(p : ℤ_[p])‖ ^ 3 := by
  obtain ⟨U,hU,hnorm⟩ := exists_matrix_lift B hB
  let T := U * scaleMatrix (p := p) s
  have hred : map PadicInt.toZMod (restrict T F) = 0 := by
    rw [map_restrict,hFG]
    exact restrict_reduction_scale_eq_zero A B s hAB U hU G₀ hG₀
  obtain ⟨G,hG,he⟩ := exists_homogeneous_quotient (restrict T F)
    (homogeneous_restrict T F hF) hred
  refine ⟨T,G,hG,he,?_⟩
  simp only [T,Matrix.det_mul,norm_mul,hnorm,one_mul,det_scaleMatrix,hs,norm_pow]

/-- A reduced cubic with no nonsingular nonzero zero admits one exact
integral descent step. This includes residue characteristics two and three. -/
theorem exists_step (hn : 3 ≤ n)
    (F : MvPolynomial (Fin n) ℤ_[p]) (hF : F.IsHomogeneous 3)
    (hno : ¬ ∃ z : Fin n → ZMod p, z ≠ 0 ∧
      eval z (map PadicInt.toZMod F) = 0 ∧
      gradient (map PadicInt.toZMod F) z ≠ 0) :
    ∃ (T : Matrix (Fin n) (Fin n) ℤ_[p]) (G : MvPolynomial (Fin n) ℤ_[p]),
      G.IsHomogeneous 3 ∧ restrict T F = C (p : ℤ_[p]) * G ∧
      ‖T.det‖ = ‖(p : ℤ_[p])‖ ^ 3 := by
  obtain ⟨m,hm,A,G,hG,hFG⟩ :=
    FiniteFieldCubicOrder.exists_linearForms_of_no_nonsingular_zero n
      (map PadicInt.toZMod F) (hF.map _) hno
  obtain ⟨B,s,hB,hs,hAB⟩ := FiniteMatrixActiveCoordinates.exists_coordinates A hm hn
  exact exists_step_of_coordinates F hF A G hG hFG B hB s hs hAB

end CubicTenVariables.PadicCubicDescent
