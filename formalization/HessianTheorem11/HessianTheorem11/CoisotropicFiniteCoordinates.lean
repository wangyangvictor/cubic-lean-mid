import HessianTheorem11.InvariantRadialWeight
import HessianTheorem11.RadicalPencilCoordinates
import HessianTheorem11.ExtremalWeightNormalObstruction

/-! Reindex the actual block basis into the finite coordinate system used
by polynomial restriction and rational unipotent transport. -/
noncomputable section
namespace HessianTheorem11
open Matrix MvPolynomial Module
namespace CoisotropicBasis.Data
variable {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d q)

def finiteIndexEquiv : CoisotropicBasis.Index m d q ≃ Fin n :=
  (Fintype.equivFin _).trans (finCongr (by simpa using (finrank_eq_card_basis D.basis).symm))

def finiteBasis : Basis (Fin n) GeometricField (GeometricPoint n) :=
  D.basis.reindex D.finiteIndexEquiv

def finiteRadial : Fin n := D.finiteIndexEquiv (Sum.inr (Sum.inr (Sum.inl D.radial)))

def finiteRadicalIndices : Finset (Fin n) :=
  Finset.univ.image (fun i : Fin m => D.finiteIndexEquiv (Sum.inl i))

def finiteNormalIndices : Finset (Fin n) :=
  Finset.univ.image (fun i : Fin d => D.finiteIndexEquiv (Sum.inr (Sum.inr (Sum.inr i))))

def finiteWeight (wB : Fin q → ℤ) : Fin n → ℤ :=
  fun i => D.invariantRadialWeight wB (D.finiteIndexEquiv.symm i)

theorem finiteBasis_radial : D.finiteBasis D.finiteRadial = x := by
  simpa only [finiteBasis,finiteRadial,Basis.reindex_apply,Equiv.symm_apply_apply] using D.radial_eq

theorem finiteRadical_image :
    D.finiteBasis '' (D.finiteRadicalIndices : Set (Fin n)) = Set.range D.radicalVector := by
  classical
  ext v
  constructor
  · rintro ⟨j,hj,rfl⟩
    change j∈Finset.univ.image (fun i : Fin m => D.finiteIndexEquiv (Sum.inl i)) at hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
    exact ⟨i,by simp [finiteBasis,radicalVector]⟩
  · rintro ⟨i,rfl⟩
    refine ⟨D.finiteIndexEquiv (Sum.inl i),?_,?_⟩
    · exact (show D.finiteIndexEquiv (Sum.inl i)∈D.finiteRadicalIndices from
        Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    · simp [finiteBasis,radicalVector]

theorem finiteRadical_span : Submodule.span GeometricField
    (D.finiteBasis '' (D.finiteRadicalIndices : Set (Fin n))) =
      LinearMap.ker (hessian F x).mulVecLin := by
  rw [D.finiteRadical_image,← D.radicalMatrix_range,Matrix.range_mulVecLin]
  rfl

theorem finite_coordinate_kernel_iff (v : GeometricPoint n) :
    (hessian (PolynomialRestriction.restrict (basisMatrix D.finiteBasis) F)
      (Pi.single D.finiteRadial 1)).mulVec v=0 ↔
        ∀i,i∉D.finiteRadicalIndices→v i=0 := by
  rw [PolynomialRestriction.hessian_restrict,basisMatrix_mulVec_single,D.finiteBasis_radial,
    matrix_congruence_kernel_iff _ _ (basisMatrix_injective D.finiteBasis),basisMatrix_mulVec_eq]
  change D.finiteBasis.equivFun.symm v ∈ LinearMap.ker (hessian F x).mulVecLin ↔ _
  rw [← D.finiteRadical_span]
  exact basis_coordinates_mem_span D.finiteBasis D.finiteRadicalIndices v

theorem finiteNormal_card : D.finiteNormalIndices.card=d := by
  classical
  rw [finiteNormalIndices,Finset.card_image_of_injective]
  · simp
  · intro i j h
    simpa using D.finiteIndexEquiv.injective h

theorem finiteWeight_radial (wB : Fin q → ℤ) : D.finiteWeight wB D.finiteRadial = -2 := by
  simp [finiteWeight,finiteRadial,invariantRadialWeight]

theorem finiteWeight_radical (wB : Fin q → ℤ) (i : Fin n) (hi : i∈D.finiteRadicalIndices) :
    D.finiteWeight wB i = -2 := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
  simp [finiteWeight,invariantRadialWeight]

theorem finiteWeight_normal (wB : Fin q → ℤ) (i : Fin n) (hi : i∈D.finiteNormalIndices) :
    D.finiteWeight wB i = 4 := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
  simp [finiteWeight,invariantRadialWeight]

theorem finiteWeight_minimum (wB : Fin q → ℤ) (hwB : ∀i,0≤wB i) (i : Fin n) :
    -2≤D.finiteWeight wB i := by
  dsimp only [finiteWeight]
  rcases he : D.finiteIndexEquiv.symm i with j|(j|(j|j))
  · norm_num [invariantRadialWeight]
  · exact (by norm_num : (-2:ℤ)≤0).trans (hwB j)
  · simp only [invariantRadialWeight,Sum.elim_inl,Sum.elim_inr]
    split_ifs <;> norm_num
  · norm_num [invariantRadialWeight]

theorem finiteWeight_minimum_only (wB : Fin q → ℤ) (hwB : ∀i,0≤wB i)
    (i : Fin n) (hi : D.finiteWeight wB i = -2) :
    i∈D.finiteRadicalIndices ∨ i=D.finiteRadial := by
  classical
  dsimp only [finiteWeight] at hi
  rcases he : D.finiteIndexEquiv.symm i with j|(j|(j|j))
  · left
    have hj : D.finiteIndexEquiv (Sum.inl j)=i := by rw [← he]; simp
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩
  · rw [he] at hi
    change wB j = -2 at hi
    have h := hwB j
    omega
  · rw [he] at hi
    change (if j=D.radial then (-2:ℤ) else 0) = -2 at hi
    have hj : j=D.radial := by split_ifs at hi <;> omega
    right
    change i=D.finiteIndexEquiv _
    rw [← hj,← he,Equiv.apply_symm_apply]
  · rw [he] at hi
    norm_num [invariantRadialWeight] at hi

theorem sum_finiteWeight (wB : Fin q → ℤ) : ∑i,D.finiteWeight wB i =
    -2*(m:ℤ)+(∑i,wB i)-2+4*(d:ℤ) := by
  change (∑i,D.invariantRadialWeight wB (D.finiteIndexEquiv.symm i))=_
  rw [D.finiteIndexEquiv.symm.sum_comp]
  exact D.sum_invariantRadialWeight wB

end CoisotropicBasis.Data
end HessianTheorem11
