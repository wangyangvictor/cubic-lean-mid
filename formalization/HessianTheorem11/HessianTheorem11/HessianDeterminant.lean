import HessianTheorem11.TextbookGeometry
import HessianTheorem11.ConcentrationLinearAlgebra
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
An anisotropic rational cubic has a nonzero actual Hessian determinant.
The input is solely the general determinantal tangent formula over the base
field, for arbitrary symmetric linear matrix pencils and arbitrary point sets.
The maximum-rank rational point and the polynomial determinant are constructed
from the actual Hessian. No nonzero-determinant premise is accepted.
-/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

/-- The standard symmetric determinantal tangent theorem over any field.
The affine source dimension and matrix size are independent; no cubic,
anisotropy, or Hessian occurs in the input. -/
structure DeterminantalTangentOver (K : Type*) [Field K] : Prop where
  tangent_kernel_pairing : ∀ {n m : ℕ}
    (M : (Fin n → K) →ₗ[K] Matrix (Fin m) (Fin m) K),
    (∀ z, (M z).transpose = M z) →
    ∀ (Z : Set (Fin n → K)) (x : Fin n → K), x ∈ Z →
      (∀ y ∈ Z, (M y).rank ≤ (M x).rank) →
      ∀ t ∈ affineTangentSpace Z x,
      ∀ u ∈ LinearMap.ker (M x).mulVecLin,
      ∀ v ∈ LinearMap.ker (M x).mulVecLin,
        dotProduct u ((M t).mulVec v) = 0

/-- Specialization recovers the existing geometric determinantal input. -/
theorem DeterminantalTangentOver.toGeometric
    (DT : DeterminantalTangentOver GeometricField) : SymmetricDeterminantalTangentInput where
  tangent_kernel_pairing := DT.tangent_kernel_pairing

section Linear
variable {K : Type*} [Field K] {n a b : ℕ}

/-- A matrix-valued function on affine points attains its maximum rank.
This uses only bounded natural-number ranks, not algebraic geometry. -/
theorem exists_maximal_matrix_rank
    (M : (Fin n → K) → Matrix (Fin a) (Fin b) K) :
    ∃ x, ∀ y, (M y).rank ≤ (M x).rank := by
  let S : Set ℕ := Set.range (fun x => (M x).rank)
  have hS : S.Nonempty := ⟨(M 0).rank, 0, rfl⟩
  have hb : BddAbove S := by
    refine ⟨b, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact Matrix.rank_le_width (A := M x)
  obtain ⟨x, hx⟩ := Nat.sSup_mem hS hb
  change (M x).rank = sSup S at hx
  refine ⟨x, ?_⟩
  intro y
  rw [hx]
  exact le_csSup hb ⟨y, rfl⟩

variable [Infinite K]

/-- Over an infinite field, a polynomial vanishing on all affine points is
zero. This explicitly identifies the full vanishing ideal of affine space. -/
theorem vanishingIdeal_univ_eq_bot :
    vanishingIdeal K (Set.univ : Set (Fin n → K)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro p hp
  apply Ideal.mem_bot.mpr
  apply MvPolynomial.funext
  intro x
  simpa using hp x (Set.mem_univ x)

theorem affineTangentSpace_univ (x : Fin n → K) :
    affineTangentSpace (Set.univ : Set (Fin n → K)) x = ⊤ := by
  apply le_antisymm le_top
  intro t _
  apply mem_affineTangentSpace.mpr
  intro p hp
  rw [vanishingIdeal_univ_eq_bot] at hp
  have hp0 : p = 0 := Ideal.mem_bot.mp hp
  simp [hp0, polynomialDifferential]

end Linear

/-- At a point with maximal rational Hessian rank the kernel is trivial:
the determinantal tangent formula on all affine space makes the cubic vanish
on every kernel vector, and anisotropy then forces that vector to be zero. -/
theorem anisotropic_exists_hessian_ker_eq_bot
    (DT : DeterminantalTangentOver ℚ) {n : ℕ} (F : AnisotropicCubic n) :
    ∃ x : Fin n → ℚ, LinearMap.ker (hessian F.polynomial x).mulVecLin = ⊥ := by
  obtain ⟨x, hmax⟩ := exists_maximal_matrix_rank (hessian F.polynomial)
  refine ⟨x, ?_⟩
  apply le_antisymm _ bot_le
  intro u hu
  change u = 0
  apply F.anisotropic
  have htensor : ∀ t ∈ (⊤ : Submodule ℚ (Fin n → ℚ)),
      ∀ v ∈ LinearMap.ker (hessian F.polynomial x).mulVecLin,
      ∀ w ∈ LinearMap.ker (hessian F.polynomial x).mulVecLin,
        polarization F.polynomial t v w = 0 := by
    intro t ht v hv w hw
    have hp := DT.tangent_kernel_pairing (hessianLinearMap F.polynomial F.homogeneous)
      (hessian_symmetric F.polynomial) Set.univ x (Set.mem_univ x)
      (fun y _ => hmax y) t (by rw [affineTangentSpace_univ]; exact ht) v hv w hw
    rw [polarization_swap_first, polarization_swap_last F.homogeneous]
    exact hp
  exact cubic_vanishes_on_kernel_of_tangent_containment F.polynomial F.homogeneous
    x ⊤ le_top htensor u hu

/-- There is an actual rational point where the Hessian has full rank. -/
theorem anisotropic_exists_hessian_full_rank
    (DT : DeterminantalTangentOver ℚ) {n : ℕ} (F : AnisotropicCubic n) :
    ∃ x : Fin n → ℚ, (hessian F.polynomial x).rank = n := by
  obtain ⟨x, hx⟩ := anisotropic_exists_hessian_ker_eq_bot DT F
  refine ⟨x, ?_⟩
  have hr := (hessian F.polynomial x).mulVecLin.finrank_range_add_finrank_ker
  rw [hx, finrank_bot, add_zero] at hr
  simpa [Matrix.rank] using hr

/-- The full-rank point gives a nonzero determinant value over the rationals. -/
theorem anisotropic_exists_hessian_det_ne_zero
    (DT : DeterminantalTangentOver ℚ) {n : ℕ} (F : AnisotropicCubic n) :
    ∃ x : Fin n → ℚ, (hessian F.polynomial x).det ≠ 0 := by
  obtain ⟨x, hx⟩ := anisotropic_exists_hessian_ker_eq_bot DT F
  refine ⟨x, ?_⟩
  intro hd
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have huk : u ∈ LinearMap.ker (hessian F.polynomial x).mulVecLin := hu
  rw [hx] at huk
  exact hu0 (by simpa using huk)

section Determinant
variable {K : Type*} [CommRing K] {n : ℕ}

/-- The determinant of the matrix of actual second partial polynomials. -/
def hessianDeterminantPolynomial (F : MvPolynomial (Fin n) K) :
    MvPolynomial (Fin n) K := (hessianPolynomial F).det

@[simp] theorem eval_hessianDeterminantPolynomial
    (F : MvPolynomial (Fin n) K) (x : Fin n → K) :
    eval x (hessianDeterminantPolynomial F) = (hessian F x).det := by
  exact (eval x).map_det (hessianPolynomial F)

/-- Forming the Hessian determinant commutes with change of coefficient ring. -/
theorem map_hessianDeterminantPolynomial
    {L : Type*} [CommRing L] (φ : K →+* L) (F : MvPolynomial (Fin n) K) :
    map φ (hessianDeterminantPolynomial F) = hessianDeterminantPolynomial (map φ F) := by
  change (map φ) (hessianPolynomial F).det = (hessianPolynomial (map φ F)).det
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [hessianPolynomial, pderiv_map]

/-- The Leibniz formula makes a size-`m` determinant of homogeneous linear
entries homogeneous of degree `m`, including when the determinant is zero. -/
theorem determinant_isHomogeneous_of_linear_entries
    {σ : Type*} {m : ℕ} (M : Matrix (Fin m) (Fin m) (MvPolynomial σ K))
    (hM : ∀ i j, (M i j).IsHomogeneous 1) : M.det.IsHomogeneous m := by
  classical
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro s _
  have hp : (∏ i, M (s i) i).IsHomogeneous m := by
    simpa using IsHomogeneous.prod Finset.univ (fun i => M (s i) i)
      (fun _ => 1) (fun i _ => hM (s i) i)
  simpa using hp.C_mul (((Equiv.Perm.sign s : ℤ) : K))

theorem hessianDeterminantPolynomial_isHomogeneous
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3) :
    (hessianDeterminantPolynomial F).IsHomogeneous n := by
  apply determinant_isHomogeneous_of_linear_entries
  intro i j
  exact hF.pderiv.pderiv

theorem hessianDeterminantPolynomial_totalDegree_le
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3) :
    (hessianDeterminantPolynomial F).totalDegree ≤ n :=
  (hessianDeterminantPolynomial_isHomogeneous hF).totalDegree_le

end Determinant

/-- Source Lemma 5.2 for the actual Hessian determinant polynomial. -/
theorem anisotropic_hessianDeterminantPolynomial_ne_zero
    (DT : DeterminantalTangentOver ℚ) {n : ℕ} (F : AnisotropicCubic n) :
    hessianDeterminantPolynomial F.polynomial ≠ 0 := by
  obtain ⟨x, hx⟩ := anisotropic_exists_hessian_det_ne_zero DT F
  intro hz
  apply hx
  rw [← eval_hessianDeterminantPolynomial, hz, map_zero]

/-- The same determinant remains nonzero after extension to the geometric field. -/
theorem geometric_hessianDeterminantPolynomial_ne_zero
    (DT : DeterminantalTangentOver ℚ) {n : ℕ} (F : AnisotropicCubic n) :
    hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0 := by
  rw [geometricPolynomial, ← map_hessianDeterminantPolynomial]
  intro hz
  apply anisotropic_hessianDeterminantPolynomial_ne_zero DT F
  apply MvPolynomial.map_injective (algebraMap ℚ GeometricField)
    (algebraMap ℚ GeometricField).injective
  simpa using hz

theorem anisotropic_hessianDeterminantPolynomial_totalDegree
    (DT : DeterminantalTangentOver ℚ) {n : ℕ} (F : AnisotropicCubic n) :
    (hessianDeterminantPolynomial F.polynomial).totalDegree = n :=
  (hessianDeterminantPolynomial_isHomogeneous F.homogeneous).totalDegree
    (anisotropic_hessianDeterminantPolynomial_ne_zero DT F)

theorem geometric_hessianDeterminantPolynomial_totalDegree
    (DT : DeterminantalTangentOver ℚ) {n : ℕ} (F : AnisotropicCubic n) :
    (hessianDeterminantPolynomial (geometricPolynomial F.polynomial)).totalDegree = n :=
  (hessianDeterminantPolynomial_isHomogeneous
    (geometric_homogeneous F.homogeneous)).totalDegree
    (geometric_hessianDeterminantPolynomial_ne_zero DT F)

end HessianTheorem11
