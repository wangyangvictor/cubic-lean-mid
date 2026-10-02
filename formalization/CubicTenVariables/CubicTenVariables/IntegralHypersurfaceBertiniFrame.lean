import CubicTenVariables.IntegralHypersurfaceSectionCoordinates
import TranslatedDepthSeven.PrincipalHomogeneousHypersurfaceDegreeInternal

/-!
# A literal Bertini frame for a hypersurface of arbitrary degree

The projective Bertini construction already supplies a prime saturated
hyperplane section.  This file removes the cubic-only degree literal from the
last elimination step.  For a hypersurface of degree at least two, an
irreducible equation cannot disappear after eliminating the linear equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000
noncomputable section

namespace CubicTenVariables.IntegralHypersurfaceBertiniFrame

open MvPolynomial TranslatedDepthSeven HessianTheorem11
open HessianTheorem11.PolynomialRestriction
open IntegralHypersurfaceSectionCoordinates
open IntegralHypersurfaceSectionElimination
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

/-- An irreducible homogeneous equation of degree at least two cannot vanish
after eliminating one homogeneous linear coordinate. -/
theorem elimination_ne_zero_of_irreducible
    {K σ : Type*} [Field K] [Fintype σ]
    {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Option σ) K) (hF : F.IsHomogeneous d)
    (hI : Irreducible F) (l : MvPolynomial σ K) (hl : l.IsHomogeneous 1) :
    optionLinearEliminationAlgHom l F ≠ 0 := by
  classical
  let L : MvPolynomial (Option σ) K := X none - rename some l
  have hLhom : L.IsHomogeneous 1 :=
    (isHomogeneous_X K none).sub hl.rename_isHomogeneous
  have hLcoeff : coeff (Finsupp.single none 1) L = 1 := by
    simp only [L, coeff_sub, coeff_X]
    rw [coeff_rename_eq_zero some l _ (by
      intro m hm
      have hh := congrArg (fun a : Option σ →₀ ℕ => a none) hm
      change (m.mapDomain some) none = (Finsupp.single none 1) none at hh
      rw [Finsupp.mapDomain_notin_range m none (by simp), Finsupp.single_eq_same] at hh
      exact (zero_ne_one hh).elim)]
    ring
  have hLne : L ≠ 0 := by
    intro h
    simp only [h, coeff_zero, zero_ne_one] at hLcoeff
  have hLdeg : L.totalDegree = 1 := hLhom.totalDegree hLne
  have hLunit : ¬ IsUnit L := by
    intro h
    have hh := (isUnit_iff_totalDegree_of_isReduced.mp h).2
    omega
  intro hzero
  have hmem : F ∈ RingHom.ker (optionLinearEliminationAlgHom l) := hzero
  rw [ker_optionLinearEliminationAlgHom] at hmem
  have hdiv : L ∣ F := Ideal.mem_span_singleton.mp hmem
  have ha : Associated F L := (hI.dvd_iff.mp hdiv).resolve_left hLunit
  have hdeg := totalDegree_le_of_dvd_of_isDomain ha.dvd hLne
  rw [hF.totalDegree hI.ne_zero, hLdeg] at hdeg
  omega

/-- Eliminate the literal prime saturated section in arbitrary degree. -/
theorem exists_integral_frame_of_prime_saturation
    {K : Type*} [Field K] {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d)
    (F L : MvPolynomial (Fin (n + 1)) K)
    (hF : F.IsHomogeneous d) (hI : Irreducible F)
    (hL : L.IsHomogeneous 1) (hLne : L ≠ 0)
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (hJ : J.IsPrime)
    (hle : Ideal.span ({F} : Set _) ⊔ Ideal.span ({L} : Set _) ≤ J)
    (hsat : ∀ P ∈ J, ∀ i : Fin (n + 1), ∃ a : ℕ,
      X i ^ a * P ∈ Ideal.span ({F} : Set _) ⊔ Ideal.span ({L} : Set _)) :
    ∃ B : Matrix (Fin (n + 1)) (Fin n) K,
      Function.Injective B.mulVec ∧ restrict B F ≠ 0 ∧
      (restrict B F).IsHomogeneous d ∧
      IsDomain (MvPolynomial (Fin n) K ⧸ Ideal.span ({restrict B F} : Set _)) := by
  classical
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨i, hi⟩ := exists_linear_coefficient_ne_zero_of_totalDegree_one L
    (hL.totalDegree hLne)
  let e : Fin (n + 1) ≃ Option (Fin n) :=
    (Equiv.swap i 0).trans (_root_.finSuccEquiv n)
  have hei : e i = none := by simp [e]
  let E := renameEquiv K e
  let Fo := E F
  let Lo := E L
  let Jo := J.map E
  have hLo : Lo.IsHomogeneous 1 := hL.rename_isHomogeneous
  have hcoeff : coeff (Finsupp.single none 1) Lo ≠ 0 := by
    have hh := coeff_rename_mapDomain e e.injective L (Finsupp.single i 1)
    have hhne : coeff ((Finsupp.single i 1).mapDomain e) (rename e L) ≠ 0 := by
      rw [hh]
      exact hi
    simpa only [Lo, E, renameEquiv_apply, Finsupp.mapDomain_single, hei] using hhne
  obtain ⟨l, hl, hspan⟩ := exists_monic_equation Lo hLo hcoeff
  have hT : (Ideal.span ({F} : Set _) ⊔ Ideal.span ({L} : Set _)).map E =
      Ideal.span ({Fo} : Set _) ⊔ Ideal.span ({X none - rename some l} : Set _) := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span,
      Set.image_singleton, Set.image_singleton]
    exact congrArg (Ideal.span ({Fo} : Set _) ⊔ ·) hspan
  have hle' : Ideal.span ({Fo} : Set _) ⊔
      Ideal.span ({X none - rename some l} : Set _) ≤ Jo := by
    rw [← hT]
    exact Ideal.map_mono hle
  have hsat' : ∀ P ∈ Jo, ∀ o : Option (Fin n), ∃ a : ℕ,
      X o ^ a * P ∈ Ideal.span ({Fo} : Set _) ⊔
        Ideal.span ({X none - rename some l} : Set _) := by
    intro P hP o
    obtain ⟨a, ha⟩ := bertini_coordinate_saturation_map_renameEquiv e
      (Ideal.span ({F} : Set _) ⊔ Ideal.span ({L} : Set _)) J hsat P hP o
    exact ⟨a, hT ▸ ha⟩
  letI : J.IsPrime := hJ
  have hJo : Jo.IsPrime := by dsimp only [Jo]; infer_instance
  have hdomain := eliminated_quotient_isDomain Fo l Jo hJo hle' hsat'
  have hFo : Fo.IsHomogeneous d := hF.rename_isHomogeneous
  have hFoI : Irreducible Fo := hI.map E.toMulEquiv
  obtain ⟨B, hB, hBF⟩ := exists_frame_for_elimination e l hl
  refine ⟨B, hB, ?_, homogeneous_restrict B F hF, ?_⟩
  · rw [hBF]
    exact elimination_ne_zero_of_irreducible hd Fo hFo hFoI l hl
  · rw [hBF]
    exact hdomain

/-- A geometrically integral projective surface hypersurface has an actual
integral hyperplane frame over an algebraically closed extension.  The frame,
restricted equation, and principal quotient are all literal. -/
theorem exists_integral_surface_hyperplane_frame_nonzero
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous d) (hirr : Irreducible F) :
    ∃ (L : Type u) (hL : Field L),
      letI : Field L := hL
      ∃ hA : Algebra K L,
        letI : Algebra K L := hA
        IsAlgClosed L ∧
        ∃ B : Matrix (Fin 4) (Fin 3) L,
          Function.Injective B.mulVec ∧
          restrict B (map (algebraMap K L) F) ≠ 0 ∧
          (restrict B (map (algebraMap K L) F)).IsHomogeneous d ∧
          IsDomain (MvPolynomial (Fin 3) L ⧸
            Ideal.span ({restrict B (map (algebraMap K L) F)} : Set _)) := by
  classical
  let I : Ideal (MvPolynomial (Fin 4) K) := Ideal.span {F}
  have hI : I.IsPrime := (Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime
  have hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin 4) K) := by
    apply Ideal.homogeneous_span
    rintro f (rfl : f = F)
    exact ⟨d, hF⟩
  have hcert := hasProjectiveDimensionDegree_principal_homogeneous F hF
    hirr.ne_zero (by omega) hI
  obtain ⟨L, hL, hLdata⟩ := projectiveGenericIntegralHyperplaneSectionExists
    K 3 2 I (by omega) hI hIhom hcert.1
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
  have hGirr : Irreducible G :=
    ((Ideal.span_singleton_prime hGne).mp hIext).irreducible
  have hellne : ell ≠ 0 := by
    intro he
    apply hell
    rw [he]
    exact Ideal.zero_mem _
  obtain ⟨B, hB, hne, hhom, hdomain⟩ :=
    exists_integral_frame_of_prime_saturation (by omega : 2 ≤ 3) hd
      G ell (hF.map _) hGirr hellhom hellne J hJ hle hsat
  exact ⟨L, hL, hA, hclosed, B, hB, hne, hhom, hdomain⟩

/-- The original Bertini-frame interface, retaining its previous conclusion. -/
theorem exists_integral_surface_hyperplane_frame
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous d) (hirr : Irreducible F) :
    ∃ (L : Type u) (hL : Field L),
      letI : Field L := hL
      ∃ hA : Algebra K L,
        letI : Algebra K L := hA
        IsAlgClosed L ∧
        ∃ B : Matrix (Fin 4) (Fin 3) L,
          Function.Injective B.mulVec ∧
          (restrict B (map (algebraMap K L) F)).IsHomogeneous d ∧
          IsDomain (MvPolynomial (Fin 3) L ⧸
            Ideal.span ({restrict B (map (algebraMap K L) F)} : Set _)) := by
  obtain ⟨L, hL, hdata⟩ :=
    exists_integral_surface_hyperplane_frame_nonzero hd F hF hirr
  letI : Field L := hL
  obtain ⟨hA, hdata⟩ := hdata
  letI : Algebra K L := hA
  obtain ⟨hclosed, B, hB, _hne, hhom, hdomain⟩ := hdata
  exact ⟨L, hL, hA, hclosed, B, hB, hhom, hdomain⟩

end CubicTenVariables.IntegralHypersurfaceBertiniFrame
