import HessianTheorem11.WittPairingTuple
import HessianTheorem11.SingularWittWeights
import HessianTheorem11.QuadraticActiveBasis

/-! The isotropic deficient-span cases, from actual polynomial pairing
identities to the actual singular polarization weight obstruction. -/
noncomputable section
namespace HessianTheorem11.SingularWittExclusion
open Module MvPolynomial WittSubspaceBasis WittQuadraticTuple SingularWittWeights
variable {K : Type*} [Field K] [CharZero K] {n s r l k : ℕ}
variable {B : LinearMap.BilinForm K (Fin 5 → K)} {U : Submodule K (Fin 5 → K)}

/-- Actual tensor coordinates of the cubic in the constructed ambient
basis. This records concrete identities; the source extraction constructs it. -/
structure Coordinates (F : MvPolynomial (Fin n) K) (D : Data B U r l k)
    (p : Fin 5 → MvPolynomial (Fin s) K) (ba : Basis (Fin s) K (Fin s → K)) where
  basis : Basis (SingularWittWeights.Index s r l k) K (Fin n → K)
  radial_kernel : (hessian F (basis radial)).mulVec (basis radial) = 0
  tangent_kernel : ∀ i, (hessian F (basis radial)).mulVec (basis (tangent i)) = 0
  tangent_tensor : ∀ i j a, polarization F (basis (tangent i)) (basis (tangent j)) (basis (tangent a)) = 0
  radial_tensor : ∀ i j, polarization F (basis radial) (basis (normal i)) (basis (normal j)) =
    B (D.basis i) (D.basis j)
  normal_tensor : ∀ i j a, polarization F (basis (tangent i)) (basis (tangent j)) (basis (normal a)) =
    polynomialDifferential (scalarTuple (B (D.basis a)) p) (ba j) (ba i)

theorem rank_zero_impossible
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (D : Data B U 0 l k) (hB : B.IsSymm)
    (p : Fin 5 → MvPolynomial (Fin s) K) (hmem : ∀ x, value p x ∈ U)
    (ba : Basis (Fin s) K (Fin s → K)) (C : Coordinates F D p ba) (hs : 5 ≤ s) : False := by
  have hnormal : 0+2*l+k=5 := by simpa only [Module.finrank_pi,Fintype.card_fin] using D.ambient_dimension
  apply impossible_of_semistable F hF hsemi C.basis ∅ (by simp) hs hnormal
    C.radial_kernel C.tangent_kernel C.tangent_tensor
  · intro i j hne
    rw [C.radial_tensor] at hne
    exact D.gram_weight i j hne
  · intro i j a hne
    left
    by_contra hw
    rw [C.normal_tensor] at hne
    exact hne (pairing_differential_zero_outside_dual D hB p hmem a hw (ba j) (ba i))

theorem active_basis_impossible
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (D : Data B U r l k) (hB : B.IsSymm)
    (p : Fin 5 → MvPolynomial (Fin s) K) (hmem : ∀ x, value p x ∈ U)
    (ba : Basis (Fin s) K (Fin s → K)) (active : Finset (Fin s)) (ha : active.card ≤ 2)
    (hrad : ∀ i ∉ active, ba i ∈ polynomialTupleDifferentialRadical (regularTuple D p))
    (C : Coordinates F D p ba) (hs : 5 ≤ s) : False := by
  classical
  have hnormal : r+2*l+k=5 := by simpa only [Module.finrank_pi,Fintype.card_fin] using D.ambient_dimension
  apply impossible_of_semistable F hF hsemi C.basis active ha hs hnormal
    C.radial_kernel C.tangent_kernel C.tangent_tensor
  · intro i j hne
    rw [C.radial_tensor] at hne
    exact D.gram_weight i j hne
  · intro i j a hne
    have hder : polynomialDifferential (scalarTuple (B (D.basis a)) p) (ba j) (ba i) ≠ 0 := by
      rwa [C.normal_tensor] at hne
    obtain hw | hw := pairing_differential_nonzero_weight D hB p hmem a (ba j) (ba i) hder
    · right
      have hw6 : WittSubspaceBasis.weight a ≠ 6 := by omega
      refine ⟨hw,?_,?_⟩
      · by_contra hi
        exact hder (pairing_differential_zero_of_regular_radical D hB p hmem a hw6
          (ba j) (ba i) (hrad i hi))
      · by_contra hj
        have hswap : polarization F (C.basis (tangent j)) (C.basis (tangent i))
            (C.basis (normal a)) ≠ 0 := by rwa [polarization_swap_first]
        rw [C.normal_tensor] at hswap
        exact hswap (pairing_differential_zero_of_regular_radical D hB p hmem a hw6
          (ba i) (ba j) (hrad j hj))
    · exact Or.inl hw

theorem rank_three_impossible [IsAlgClosed K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (D : Data B U 3 l k) (hB : B.IsSymm)
    (p : Fin 5 → MvPolynomial (Fin s) K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hspan : Submodule.span K (Set.range (value p)) = U)
    (hrel : ∀ x, B (value p x) (value p x) = 0)
    (hC : ∀ ba : Basis (Fin s) K (Fin s → K), Nonempty (Coordinates F D p ba))
    (hs : 5 ≤ s) : False := by
  have hmem : ∀ x, value p x ∈ U := fun x => hspan.le (Submodule.subset_span ⟨x,rfl⟩)
  obtain ⟨ba,active,ha,hv⟩ := three_quadrics_active_basis (regularTuple D p)
    (regularTuple_homogeneous D p hp) (regularTuple_independent D p hspan)
    (regularGram D) (regularGram_symm D hB) D.regular_nonsingular
    (regular_relation D hB p hmem hrel)
  obtain ⟨C⟩ := hC ba
  exact active_basis_impossible F hF hsemi D hB p hmem ba active ha
    (fun i hi => (mem_polynomialTupleDifferentialRadical _ _).mpr (hv i hi)) C hs

end HessianTheorem11.SingularWittExclusion
