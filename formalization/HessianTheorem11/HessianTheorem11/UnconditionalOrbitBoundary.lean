import HessianTheorem11.UnconditionalFormOrbitOpen
import HessianTheorem11.ReducedRelativeGeometry

/-! The actual special-linear orbit is open in its coefficient closure,
and its actual boundary is coefficient-closed. These statements are proved
from the polynomial orbit map and generic smoothness, with no orbit-geometry
input. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitBoundary
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
  UnconditionalPolynomialOrbit UnconditionalOrbitIdeal UnconditionalGenericPointOpen
  ReducedRelative ReducedOrbitCoordinates

theorem slOrbit_eq_of_mem {n : ℕ} (F G : GeometricPolynomial n)
    (hG : G ∈ slOrbit F) : slOrbit G = slOrbit F := by
  obtain ⟨B,hB,rfl⟩ := hG
  have hu : IsUnit B.det := hB ▸ isUnit_one
  ext H
  constructor
  · rintro ⟨A,hA,rfl⟩
    exact ⟨B*A,by rw [Matrix.det_mul,hB,hA,one_mul],restrict_restrict B A F⟩
  · rintro ⟨A,hA,rfl⟩
    refine ⟨B⁻¹*A,?_,?_⟩
    · rw [Matrix.det_mul,Matrix.det_nonsing_inv,hB,Ring.inverse_one,hA,one_mul]
    · rw [restrict_restrict,← Matrix.mul_assoc,Matrix.mul_nonsing_inv B hu,Matrix.one_mul]

theorem slOrbitClosure_eq_of_mem {n : ℕ} (F G : GeometricPolynomial n)
    (hG : G ∈ slOrbit F) : slOrbitClosure G = slOrbitClosure F := by
  simp only [slOrbitClosure,slOrbit_eq_of_mem F G hG]

theorem restrict_mem_same_closure {n d : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous d) (A : Matrix (Fin n) (Fin n) GeometricField)
    (hA : A.det = 1) (G : GeometricPolynomial n) (hG : G ∈ slOrbitClosure F) :
    restrict A G ∈ slOrbitClosure F := by
  have he := slOrbitClosure_eq_of_mem F (restrict A F) ⟨A,hA,rfl⟩
  rw [← he]
  exact slOrbitClosure_restrict A (hA ▸ isUnit_one) F G hF hG

/-- Coefficient closure maps into the genuine finite affine closure of the
actual polynomial matrix orbit map. -/
theorem coefficientVector_mem_imageClosure {n d : ℕ} (F G : GeometricPolynomial n)
    (hG : G ∈ slOrbitClosure F) :
    coefficientVector (d := d) G ∈ geometricClosure
      (polynomialMap (orbitPolynomials (d := d) F) ''
        UnconditionalSpecialLinear.specialLinearLocus n) := by
  intro p hp
  change eval (coefficientVector (d := d) G) p = 0
  have he (H : GeometricPolynomial n) :
      eval (fun e => coeff e H) (rename Subtype.val p) =
        eval (coefficientVector (d := d) H) p := by
    rw [eval_rename]
    rfl
  rw [← he G]
  apply hG
  rintro H ⟨A,hA,rfl⟩
  rw [he]
  apply hp
  refine ⟨matrixPoint A,hA,?_⟩
  simp only [polynomialMap_orbitPolynomials,pointMatrix_matrixPoint]

/-- A principal coefficient neighborhood of F in the entire orbit closure
lies in the orbit itself. -/
theorem exists_principal_neighborhood_in_orbit {n d : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous d) :
    ∃ p : MvPolynomial (Fin n →₀ ℕ) GeometricField,
      eval (fun e => coeff e F) p ≠ 0 ∧
      ∀ G ∈ slOrbitClosure F, eval (fun e => coeff e G) p ≠ 0 → G ∈ slOrbit F := by
  classical
  let Z := UnconditionalSpecialLinear.specialLinearLocus n
  let P := orbitPolynomials (d := d) F
  obtain ⟨x,hx,hopen⟩ := exists_open_point P Z
    (UnconditionalSpecialLinear.specialLinearLocus_closed n)
    (UnconditionalSpecialLinear.specialLinearLocus_irreducible n)
  let A₀ := pointMatrix x
  have hA₀ : A₀.det = 1 := hx
  have hu : IsUnit A₀.det := hA₀ ▸ isUnit_one
  obtain ⟨g,hg,hsub⟩ := hopen 1 (by simp)
  refine ⟨translatedCoefficientTest A₀ g,?_,?_⟩
  · rw [eval_translatedCoefficientTest A₀ g F hF]
    simpa only [P,polynomialMap_orbitPolynomials] using hg
  · intro G hG hpG
    have hGh := slOrbitClosure_homogeneous F hF G hG
    rw [eval_translatedCoefficientTest A₀ g G hGh] at hpG
    have hy := coefficientVector_mem_imageClosure (d := d) F (restrict A₀ G)
      (restrict_mem_same_closure F hF A₀ hA₀ G hG)
    obtain ⟨z,⟨hz,_⟩,hez⟩ := hsub _ hy hpG
    have hform : restrict (pointMatrix z) F = restrict A₀ G := by
      have he := congrArg (decode (d := d)) hez
      simpa only [P,polynomialMap_orbitPolynomials,
        decode_coefficientVector _ (homogeneous_restrict (pointMatrix z) F hF),
        decode_coefficientVector _ (homogeneous_restrict A₀ G hGh)] using he
    refine ⟨pointMatrix z * A₀⁻¹,?_,?_⟩
    · have hz' : (pointMatrix z).det = 1 := hz
      rw [Matrix.det_mul,hz',one_mul,Matrix.det_nonsing_inv,hA₀,Ring.inverse_one]
    · rw [← restrict_restrict,hform,restrict_restrict,
        Matrix.mul_nonsing_inv A₀ hu,restrict_one]

/-- Every orbit point is separated from the actual orbit boundary by an
actual coefficient polynomial vanishing on that boundary. -/
theorem exists_boundary_separator {n d : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous d) (G : GeometricPolynomial n) (hG : G ∈ slOrbit F) :
    ∃ p : MvPolynomial (Fin n →₀ ℕ) GeometricField,
      coefficientVanishing (orbitBoundary F) p ∧ eval (fun e => coeff e G) p ≠ 0 := by
  have hGh : G.IsHomogeneous d := by
    obtain ⟨A,hA,rfl⟩ := hG
    exact homogeneous_restrict A F hF
  obtain ⟨p,hp,hsub⟩ := exists_principal_neighborhood_in_orbit G hGh
  refine ⟨p,?_,hp⟩
  intro H hH
  by_contra hn
  apply hH.2
  rw [← slOrbit_eq_of_mem F G hG]
  apply hsub H _ hn
  rw [slOrbitClosure_eq_of_mem F G hG]
  exact hH.1

/-- The actual boundary, rather than an auxiliary closed target, is closed
for all coefficient-polynomial equations. -/
theorem orbitBoundary_coefficientClosed {n d : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous d) : coefficientClosed (orbitBoundary F) := by
  intro G hG
  have hc : G ∈ slOrbitClosure F := by
    intro p hp
    apply hG p
    intro H hH
    exact hH.1 p hp
  refine ⟨hc,?_⟩
  intro ho
  obtain ⟨p,hp,hne⟩ := exists_boundary_separator F hF G ho
  exact hne (hG p hp)

/-- Relative openness expressed in the original coefficient-space
closed-set convention. -/
theorem orbit_relatively_open {n d : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous d) :
    ∃ C, coefficientClosed C ∧ slOrbit F = slOrbitClosure F \ C := by
  refine ⟨orbitBoundary F,orbitBoundary_coefficientClosed F hF,?_⟩
  ext G
  constructor
  · intro hG
    exact ⟨slOrbit_subset_closure F hG,fun h => h.2 hG⟩
  · rintro ⟨hc,hn⟩
    by_contra ho
    exact hn ⟨hc,ho⟩

/-- The former ordinary orbit-boundary package is constructed without
external geometric or invariant-theoretic inputs. -/
def orbitBoundaryClosedInput : OrbitBoundaryClosedInput GeometricField where
  closed_boundary := orbitBoundary_coefficientClosed

end HessianTheorem11.UnconditionalOrbitBoundary
