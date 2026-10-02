import HessianTheorem11.SingularWittExclusion
import HessianTheorem11.WittRegularExclusion
import HessianTheorem11.QuadraticCoordinateTransport

/-! Deficient normal span is impossible once its actual ambient coordinate
identities have been constructed. All rank, factorization and weight cases
are discharged here. The following geometric wrapper supplies the coordinates. -/
noncomputable section
namespace HessianTheorem11
open Module MvPolynomial WittSubspaceBasis WittQuadraticTuple SingularWittExclusion
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n s m : ℕ}

theorem linearIndependent_of_value_span_top
    (p : Fin m → MvPolynomial (Fin s) K)
    (hspan : Submodule.span K (Set.range (value p)) = ⊤) : LinearIndependent K p := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let L : (Fin m → K) →ₗ[K] K := (dotProductBilin K K) c
  have hker : Submodule.span K (Set.range (value p)) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    have he := congrArg (eval x) hc
    change dotProduct c (value p x) = 0
    simpa only [map_sum,MvPolynomial.smul_eq_C_mul,map_mul,eval_C,map_zero,dotProduct] using he
  rw [hspan] at hker
  have he := hker (Submodule.mem_top : Pi.single j 1 ∈ (⊤ : Submodule K (Fin m → K)))
  change dotProduct c (Pi.single j 1) = 0 at he
  simpa using he

/-- Full algebraic deficient-span argument. The coordinate premise is an
explicit family of bases and identities of the original cubic, constructed
by `SingularWittCoordinates`; it is not an AG or source theorem input. -/
theorem singular_normal_tuple_independent_of_coordinates
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (p : Fin 5 → MvPolynomial (Fin s) K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (B : LinearMap.BilinForm K (Fin 5 → K)) (hB : B.IsSymm) (hnB : B.Nondegenerate)
    (hrel : ∀ x, B (value p x) (value p x) = 0)
    (hcommon : polynomialTupleDifferentialRadical p = ⊥) (hs : 5 ≤ s)
    (hcoord : ∀ r l k,
      ∀ D : Data B (Submodule.span K (Set.range (value p))) r l k,
      ∀ ba : Basis (Fin s) K (Fin s → K), Nonempty (Coordinates F D p ba)) :
    LinearIndependent K p := by
  classical
  by_contra hli
  let U := Submodule.span K (Set.range (value p))
  have hproper : finrank K U ≤ 4 := by
    have hne : U ≠ ⊤ := fun h => hli (linearIndependent_of_value_span_top p h)
    have hd := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hne)
    simp only [finrank_top,Module.finrank_pi,Fintype.card_fin] at hd
    omega
  obtain ⟨r,l,k,⟨D⟩⟩ := WittSubspaceBasis.exists_data B hB hnB U
  have hcases := deficient_five_cases D hB p rfl hrel (Fintype.card_fin 5) hproper
  rcases hcases with ⟨rfl,hl⟩ | ⟨rfl,hl⟩ | ⟨rfl,rfl⟩
  · let ba := Pi.basisFun K (Fin s)
    obtain ⟨C⟩ := hcoord 0 l k D ba
    exact rank_zero_impossible F hF hsemi D hB p (fun x => Submodule.subset_span ⟨x,rfl⟩) ba C hs
  · exact rank_three_impossible F hF hsemi D hB p hp rfl hrel (hcoord 3 l k D) hs
  · exact regular_three_four_excluded D hB p hp rfl hrel hcommon hs (Or.inr rfl)

namespace GradedIndexCoordinates

theorem rawTuple_independent {r s n : ℕ} {T : Finset (Fin n)} {c : Fin n}
    (D : GradedIndexCoordinates T c r s)
    (p : (↑Tᶜ : Type) → MvPolynomial (↑(T.erase c) : Type) K)
    (hp : LinearIndependent K (D.normalTuple p)) : LinearIndependent K p := by
  let E := renameEquiv K D.tangent.symm
  have he := hp.comp D.normal.symm D.normal.symm.injective
  have hef : D.normalTuple p ∘ D.normal.symm = E.toLinearMap ∘ p := by
    funext i
    change rename D.tangent.symm (p (D.normal (D.normal.symm i))) = _
    rw [D.normal.apply_symm_apply]
    rfl
  have he' : LinearIndependent K (E.toLinearMap ∘ p) := hef ▸ he
  exact LinearIndependent.of_comp E.toLinearMap he'

end GradedIndexCoordinates

theorem quadraticRelation_toBilin_value
    (A : Matrix (Fin 5) (Fin 5) K) (p : Fin 5 → MvPolynomial (Fin s) K)
    (hrel : TangentHessianRank.quadraticRelation A p = 0) (x : Fin s → K) :
    Matrix.toBilin' A (value p x) (value p x) = 0 := by
  have he := congrArg (eval x) hrel
  simp only [TangentHessianRank.quadraticRelation,map_sum,map_mul,eval_C,map_zero] at he
  convert he using 1
  simp only [Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end HessianTheorem11
