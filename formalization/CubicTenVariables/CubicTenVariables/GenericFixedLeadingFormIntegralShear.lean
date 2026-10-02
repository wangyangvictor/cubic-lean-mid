import CubicTenVariables.FixedLeadingFormIntegralShear

/-!
# A fixed integral slicing shear in every dimension needed by the cone count

The generic projective Bertini construction and its elimination theorem
already work in arbitrary dimension. This file exposes the corresponding
fixed-form rational graph and integral shear, using only the existing
homogeneous hypersurface integrality-open input. It introduces no family
slicing certificate or saturated matrix-open assumption.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
noncomputable section
namespace CubicTenVariables.GenericFixedLeadingFormIntegralShear
open MvPolynomial TranslatedDepthSeven
open HessianTheorem11.PolynomialRestriction
open HessianTheorem11.PolynomialWeightTransport
open FixedLeadingFormIntegralShear
open scoped Matrix BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

/-- Generic-dimensional version of the proved hypersurface frame theorem. -/
theorem exists_integral_hyperplane_frame_nonzero
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    {n d : ℕ} (hn : 3 ≤ n) (hd : 2 ≤ d)
    (F : MvPolynomial (Fin (n + 1)) K)
    (hF : F.IsHomogeneous d) (hirr : Irreducible F) :
    ∃ (L : Type u) (hL : Field L),
      letI : Field L := hL
      ∃ hA : Algebra K L,
        letI : Algebra K L := hA
        IsAlgClosed L ∧
        ∃ B : Matrix (Fin (n + 1)) (Fin n) L,
          Function.Injective B.mulVec ∧
          restrict B (map (algebraMap K L) F) ≠ 0 ∧
          (restrict B (map (algebraMap K L) F)).IsHomogeneous d ∧
          IsDomain (MvPolynomial (Fin n) L ⧸
            Ideal.span ({restrict B (map (algebraMap K L) F)} : Set _)) := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, n = r + 1 := ⟨n - 1, by omega⟩
  let I : Ideal (MvPolynomial (Fin (r + 1 + 1)) K) := Ideal.span {F}
  have hI : I.IsPrime := (Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime
  have hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (r + 1 + 1)) K) := by
    apply Ideal.homogeneous_span
    rintro f (rfl : f = F)
    exact ⟨d, hF⟩
  have hcert := hasProjectiveDimensionDegree_principal_homogeneous F hF
    hirr.ne_zero (by omega) hI
  obtain ⟨L, hL, hLdata⟩ := projectiveGenericIntegralHyperplaneSectionExists
    K (r + 1) r I (by omega) hI hIhom hcert.1
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
    IntegralHypersurfaceBertiniFrame.exists_integral_frame_of_prime_saturation (by omega : 2 ≤ r + 1) hd
      G ell (hF.map _) hGirr hellhom hellne J hJ hle hsat
  exact ⟨L, hL, hA, hclosed, B, hB, hne, hhom, hdomain⟩

private theorem exists_eval_ne_zero {σ : Type*}
    (P : MvPolynomial σ ℚ) (hP : P ≠ 0) :
    ∃ x, eval x P ≠ 0 := by
  by_contra! h
  apply hP
  apply MvPolynomial.funext
  intro x
  simpa only [map_zero] using h x

/-- A full-frame integrality certificate meets the graph chart. -/
theorem exists_rational_good_graph
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {n d : ℕ} (hn : 3 ≤ n) (hd : 2 ≤ d)
    (H : MvPolynomial (Fin (n + 1)) ℚ) (hhom : H.IsHomogeneous d)
    (hirr : Published.IsAbsolutelyIrreducible H) :
    ∃ a : Fin n → ℚ,
      restrict (graphFrame a) H ≠ 0 ∧
      IsDomain (MvPolynomial (Fin n) (AlgebraicClosure ℚ) ⧸
        Ideal.span {map (algebraMap ℚ (AlgebraicClosure ℚ))
          (restrict (graphFrame a) H)}) := by
  classical
  let Ω := AlgebraicClosure ℚ
  obtain ⟨L, hL, hdata⟩ :=
    exists_integral_hyperplane_frame_nonzero
      hn hd (map (algebraMap ℚ Ω) H) (hhom.map _) hirr
  letI : Field L := hL
  obtain ⟨hA, hdata⟩ := hdata
  letI : Algebra Ω L := hA
  obtain ⟨hclosed, B, hB, hBne, _hBhom, hBdomain⟩ := hdata
  letI : IsAlgClosed L := hclosed
  let ρ : ℚ →+* L := (algebraMap Ω L).comp (algebraMap ℚ Ω)
  have hmap : map ρ H = map (algebraMap Ω L) (map (algebraMap ℚ Ω) H) := by
    rw [map_map]
  obtain ⟨Δ, hΔB, hgood⟩ :=
    HypersurfaceIntegralFrameCertificate.exists_nonzero_certificate_of_good_frame
      integralityOpen (by omega : 1 ≤ d) ρ H hhom B hB
      (by rw [hmap]; exact hBne) (by rw [hmap]; exact hBdomain)
  have hΔ : Δ ≠ 0 := fun hz => hΔB (by rw [hz, map_zero])
  let D : MvPolynomial (Fin (n + 1) × Fin n) ℚ :=
    Matrix.det (fun i j : Fin n => X (i.succ, j))
  have hD : D ≠ 0 := GenericHyperplaneFrameOpen.lowerMinor_ne_zero
  obtain ⟨b, hb⟩ := exists_eval_ne_zero (Δ * D) (mul_ne_zero hΔ hD)
  have hb' : eval b Δ ≠ 0 ∧ eval b D ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [map_mul] using hb)
  let A : Matrix (Fin (n + 1)) (Fin n) ℚ := fun i j => b (i, j)
  let M : Matrix (Fin n) (Fin n) ℚ := fun i j => A i.succ j
  have hM : M.det ≠ 0 := by
    have he : eval b D = M.det := by
      dsimp only [D]
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [M, A]
    exact he ▸ hb'.2
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  obtain ⟨a, ha⟩ := Matrix.vecMul_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det M).mpr hunit) (A 0)
  have hframe : graphFrame a * M = A := graphFrame_mul A M a (fun _ _ => rfl) ha
  have hgoodA := hgood ℚ (RingHom.id ℚ) A hb'.1
  rw [MvPolynomial.map_id] at hgoodA
  have hAne : restrict A H ≠ 0 := by
    intro hz
    have he := hgoodA.2.2.1
    rw [hz, totalDegree_zero] at he
    omega
  have hfactor : restrict A H = restrict M (restrict (graphFrame a) H) := by
    rw [restrict_restrict, hframe]
  refine ⟨a, ?_, ?_⟩
  · intro hz
    apply hAne
    rw [hfactor, hz]
    exact map_zero (aeval (linearForms M))
  · exact ReducedConeCoordinates.quotient_domain_baseChange_of_factor
      (restrict A H) (restrict (graphFrame a) H) M M⁻¹
      (Matrix.mul_nonsing_inv M hunit) hfactor hgoodA.2.2.2

/-- For one fixed rational absolutely irreducible homogeneous form in at least four
variables, an integral shear has an absolutely irreducible hyperplane section.
The only explicit literature premise is fixed-degree integrality openness. -/
theorem exists_integral_shear_absIrreducible
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {n d : ℕ} (hn : 3 ≤ n) (hd : 2 ≤ d)
    (H : MvPolynomial (Fin (n + 1)) ℚ) (hhom : H.IsHomogeneous d)
    (hirr : Published.IsAbsolutelyIrreducible H) :
    ∃ a : Fin n → ℤ,
      Published.IsAbsolutelyIrreducible
        (rationalSpecializeFirstCoordinate 0
          (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) H)) := by
  classical
  obtain ⟨a, hane, hadomain⟩ := exists_rational_good_graph integralityOpen hn hd H hhom hirr
  let Ω := AlgebraicClosure ℚ
  let ρ : MvPolynomial (Fin n) ℚ →+* Ω :=
    eval₂Hom (algebraMap ℚ Ω) (fun i => algebraMap ℚ Ω (a i))
  have hspecial : map ρ (graphFamily H) =
      map (algebraMap ℚ Ω) (restrict (graphFrame a) H) := by
    rw [specialize_graphFamily, map_restrict]
    congr 1
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      simp [graphFrame, Matrix.map_apply, Matrix.one_apply]
  have hne : map ρ (graphFamily H) ≠ 0 := by
    rw [hspecial]
    exact fun hz => hane ((map_injective _ (algebraMap ℚ Ω).injective)
      (by simpa only [map_zero] using hz))
  obtain ⟨s, hs, hopen⟩ := integralityOpen (MvPolynomial (Fin n) ℚ) Ω n d
    (by omega : 1 ≤ d) ρ (graphFamily H)
    (homogeneous_restrict _ _ (hhom.map C)) hne (by rw [hspecial]; exact hadomain)
  have hsne : s ≠ 0 := fun hz => hs (by rw [hz, map_zero])
  obtain ⟨z, _hzbound, hz⟩ := exists_nonzero_eval_on_boundedNatGrid_over_field
    s hsne (le_refl s.totalDegree)
  let b : Fin n → ℤ := fun i => z i
  have hb : eval (fun i => (b i : ℚ)) s ≠ 0 := by
    simpa only [b, Int.cast_natCast] using hz
  have hgood := hopen ℚ (eval (fun i => (b i : ℚ))) hb
  have heval : map (eval (fun i => (b i : ℚ))) (graphFamily H) =
      restrict (graphFrame (fun i => (b i : ℚ))) H := by
    simpa only [map_id] using specialize_graphFamily (RingHom.id ℚ)
      (fun i => (b i : ℚ)) H
  rw [heval] at hgood
  have hgne : restrict (graphFrame (fun i => (b i : ℚ))) H ≠ 0 := by
    intro hz
    rw [hz, totalDegree_zero] at hgood
    omega
  have hgeone : map (algebraMap ℚ Ω)
      (restrict (graphFrame (fun i => (b i : ℚ))) H) ≠ 0 := by
    exact fun hz => hgne ((map_injective _ (algebraMap ℚ Ω).injective)
      (by simpa only [map_zero] using hz))
  refine ⟨b, ?_⟩
  rw [← restrict_graphFrame_eq_shear_slice]
  exact ((Ideal.span_singleton_prime hgeone).mp
    ((Ideal.Quotient.isDomain_iff_prime _).mp hgood.2)).irreducible


end CubicTenVariables.GenericFixedLeadingFormIntegralShear
