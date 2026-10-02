import CubicTenVariables.IntegralHypersurfaceSectionCoordinates
import TranslatedDepthSeven.PrincipalHomogeneousHypersurfaceDegreeInternal
import CubicTenVariables.ReducedVertexBaseChange
import HessianTheorem11.PolynomialWeightTransport

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.IntegralCubicBertiniFrame
open MvPolynomial TranslatedDepthSeven HessianTheorem11.PolynomialRestriction
open IntegralHypersurfaceSectionCoordinates
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

/-- A literal injective hyperplane frame with irreducible cubic restriction,
over a possibly larger algebraically closed field. Its existence follows
from the proved generic marked-incidence construction, not an input. -/
theorem exists_integral_hyperplane_frame
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (m : ℕ) (F : MvPolynomial (Fin (m+4)) K)
    (hF : F.IsHomogeneous 3) (hirr : Irreducible F) :
    ∃ (L : Type u) (hL : Field L),
      letI : Field L := hL
      ∃ hA : Algebra K L,
        letI : Algebra K L := hA
        IsAlgClosed L ∧
        ∃ B : Matrix (Fin (m+4)) (Fin (m+3)) L,
          Function.Injective B.mulVec ∧
          (restrict B (map (algebraMap K L) F)).IsHomogeneous 3 ∧
          Irreducible (restrict B (map (algebraMap K L) F)) := by
  classical
  let I : Ideal (MvPolynomial (Fin (m+4)) K) := Ideal.span {F}
  have hI : I.IsPrime := (Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime
  have hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (m+4)) K) := by
    apply Ideal.homogeneous_span
    rintro f (rfl : f = F)
    exact ⟨3, hF⟩
  have hcert := hasProjectiveDimensionDegree_principal_homogeneous F hF hirr.ne_zero
    (by decide : 0 < 3) hI
  obtain ⟨L, hL, hLdata⟩ := projectiveGenericIntegralHyperplaneSectionExists
    K (m+3) (m+2) I (by omega) hI hIhom hcert.1
  letI : Field L := hL
  obtain ⟨hA, hLdata⟩ := hLdata
  letI : Algebra K L := hA
  obtain ⟨hclosed, hIext, ell, J, hellhom, hell, hJ, _, _, hle, hsat⟩ := hLdata
  letI : IsAlgClosed L := hclosed
  let G := map (algebraMap K L) F
  have hGne : G ≠ 0 := by
    intro h
    exact hirr.ne_zero ((map_injective (algebraMap K L) (algebraMap K L).injective)
      (by simpa only [map_zero] using h))
  have hext : I.map (map (algebraMap K L)) = Ideal.span ({G} : Set _) := by
    simp only [I, Ideal.map_span, Set.image_singleton, G]
  rw [hext] at hIext hell hle hsat
  have hGirr : Irreducible G := ((Ideal.span_singleton_prime hGne).mp hIext).irreducible
  have hellne : ell ≠ 0 := by
    intro he
    apply hell
    rw [he]
    exact Ideal.zero_mem _
  obtain ⟨B, hB, hne, hhom, hdom⟩ := exists_integral_frame_of_prime_saturation
    (by omega : 2 ≤ m+3) G ell (hF.map _) hGirr hellhom hellne J hJ hle hsat
  refine ⟨L, hL, hA, hclosed, B, hB, hhom, ?_⟩
  exact ((Ideal.span_singleton_prime hne).mp
    ((Ideal.Quotient.isDomain_iff_prime _).mp hdom)).irreducible

/-- One more proved integral hyperplane cut, with its frame composed into
the original coordinates and its coefficient fields composed explicitly. -/
theorem extend_integral_frame
    {K L : Type u} [Field K] [Field L] [CharZero L] [IsAlgClosed L] [Algebra K L]
    {n m : ℕ} (F : MvPolynomial (Fin n) K)
    (B : Matrix (Fin n) (Fin (m+4)) L) (hB : Function.Injective B.mulVec)
    (hG : (restrict B (map (algebraMap K L) F)).IsHomogeneous 3)
    (hI : Irreducible (restrict B (map (algebraMap K L) F))) :
    ∃ (M : Type u) (hM : Field M),
      letI : Field M := hM
      ∃ hA : Algebra K M,
        letI : Algebra K M := hA
        CharZero M ∧ IsAlgClosed M ∧
        ∃ C : Matrix (Fin n) (Fin (m+3)) M,
          Function.Injective C.mulVec ∧
          (restrict C (map (algebraMap K M) F)).IsHomogeneous 3 ∧
          Irreducible (restrict C (map (algebraMap K M) F)) := by
  obtain ⟨M, hM, hdata⟩ := exists_integral_hyperplane_frame m
    (restrict B (map (algebraMap K L) F)) hG hI
  letI : Field M := hM
  obtain ⟨hA, hdata⟩ := hdata
  letI : Algebra L M := hA
  obtain ⟨hclosed, D, hD, hhom, hirr⟩ := hdata
  letI : CharZero M := charZero_of_injective_algebraMap (algebraMap L M).injective
  let φ : K →+* M := (algebraMap L M).comp (algebraMap K L)
  letI : Algebra K M := φ.toAlgebra
  let C := (B.map (algebraMap L M)) * D
  have hBC : Function.Injective C.mulVec := by
    intro x y hxy
    apply hD
    apply ReducedVertexBaseChange.map_frame_injective B hB
    simpa only [C, Matrix.mulVec_mulVec] using hxy
  have hpoly : restrict C (map (algebraMap K M) F) =
      restrict D (map (algebraMap L M) (restrict B (map (algebraMap K L) F))) := by
    rw [map_restrict, HessianTheorem11.PolynomialWeightTransport.restrict_restrict, map_map]
    rfl
  refine ⟨M, hM, inferInstance, inferInstance, hclosed, C, hBC, ?_, ?_⟩
  · rw [hpoly]
    exact hhom
  · rw [hpoly]
    exact hirr

/-- The actual nine-to-five-variable integral section. Four applications
of the proved generic hyperplane construction are composed into one literal
injective frame; no section-existence or geometric-integrality input remains.
The coefficient field may be enlarged. -/
theorem exists_nine_to_five_integral_frame
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (F : MvPolynomial (Fin 9) K)
    (hF : F.IsHomogeneous 3) (hirr : Irreducible F) :
    ∃ (L : Type u) (hL : Field L),
      letI : Field L := hL
      ∃ hA : Algebra K L,
        letI : Algebra K L := hA
        IsAlgClosed L ∧
        ∃ B : Matrix (Fin 9) (Fin 5) L,
          Function.Injective B.mulVec ∧
          (restrict B (map (algebraMap K L) F)).IsHomogeneous 3 ∧
          Irreducible (restrict B (map (algebraMap K L) F)) := by
  obtain ⟨L₁, hL₁, hdata₁⟩ := exists_integral_hyperplane_frame 5 F hF hirr
  letI : Field L₁ := hL₁
  obtain ⟨hA₁, hdata₁⟩ := hdata₁
  letI : Algebra K L₁ := hA₁
  obtain ⟨hclosed₁, B₁, hB₁, hhom₁, hirr₁⟩ := hdata₁
  letI : IsAlgClosed L₁ := hclosed₁
  letI : CharZero L₁ := charZero_of_injective_algebraMap (algebraMap K L₁).injective
  obtain ⟨L₂, hL₂, hdata₂⟩ := extend_integral_frame F B₁ hB₁ hhom₁ hirr₁
  letI : Field L₂ := hL₂
  obtain ⟨hA₂, hdata₂⟩ := hdata₂
  letI : Algebra K L₂ := hA₂
  obtain ⟨hchar₂, hclosed₂, B₂, hB₂, hhom₂, hirr₂⟩ := hdata₂
  letI : CharZero L₂ := hchar₂
  letI : IsAlgClosed L₂ := hclosed₂
  obtain ⟨L₃, hL₃, hdata₃⟩ := extend_integral_frame F B₂ hB₂ hhom₂ hirr₂
  letI : Field L₃ := hL₃
  obtain ⟨hA₃, hdata₃⟩ := hdata₃
  letI : Algebra K L₃ := hA₃
  obtain ⟨hchar₃, hclosed₃, B₃, hB₃, hhom₃, hirr₃⟩ := hdata₃
  letI : CharZero L₃ := hchar₃
  letI : IsAlgClosed L₃ := hclosed₃
  obtain ⟨L₄, hL₄, hdata₄⟩ := extend_integral_frame F B₃ hB₃ hhom₃ hirr₃
  letI : Field L₄ := hL₄
  obtain ⟨hA₄, hdata₄⟩ := hdata₄
  letI : Algebra K L₄ := hA₄
  obtain ⟨_, hclosed₄, B₄, hB₄, hhom₄, hirr₄⟩ := hdata₄
  exact ⟨L₄, hL₄, hA₄, hclosed₄, B₄, hB₄, hhom₄, hirr₄⟩

end CubicTenVariables.IntegralCubicBertiniFrame
