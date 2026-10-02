import CubicTenVariables.HomogeneousOriginOpen
import CubicTenVariables.CubicLinearFactorMinors
import CubicTenVariables.Literature.FiniteFieldPointCounts

/-! Irreducibility of a homogeneous cubic is open at an arbitrary good
algebraically closed specialization. The proof uses actual linear-factor
minors and homogeneous origin-only certificates. It does not assume generic
integrality, injectivity of the given specialization, or a Noetherian base. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicIrreducibilityOpen
open MvPolynomial CubicLinearFactorMinors

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A single coefficient-ring element, nonzero at the given good fiber,
preserves actual irreducibility in every algebraically closed target field. -/
theorem exists_principal_open
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (ρ : R →+* Ω) (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (hirr : Irreducible (map ρ F)) :
    ∃ s : R, ρ s ≠ 0 ∧
      ∀ (K : Type*) [Field K] [IsAlgClosed K] (τ : R →+* K), τ s ≠ 0 →
        Irreducible (map τ F) := by
  classical
  have horigin : ∀ a : Fin n → Ω,
      (∀ i, eval a (map ρ (equations F i)) = 0) → a = 0 := by
    intro a ha
    by_contra hne
    apply (not_irreducible_iff_projective_solution (map ρ F) (hF.map ρ) hirr.ne_zero).mpr
      ⟨a, hne, fun i => by simpa only [map_equations] using ha i⟩
    exact hirr
  obtain ⟨s, hs, hgood⟩ := HomogeneousOriginOpen.exists_principal_open
    ρ (equations F) degrees (equations_homogeneous F) horigin
  obtain ⟨u, hu⟩ : ∃ u, ρ (coeff u F) ≠ 0 := by
    by_contra! h
    apply hirr.ne_zero
    ext u
    simpa only [coeff_map, coeff_zero] using h u
  refine ⟨s * coeff u F, ?_, ?_⟩
  · simpa only [map_mul] using mul_ne_zero hs hu
  · intro K _ _ τ hτ
    have hh : τ s ≠ 0 ∧ τ (coeff u F) ≠ 0 :=
      mul_ne_zero_iff.mp (by simpa only [map_mul] using hτ)
    have hne : map τ F ≠ 0 := by
      intro hz
      exact hh.2 (by simpa only [coeff_map, coeff_zero] using congrArg (coeff u) hz)
    by_contra hred
    obtain ⟨a, ha, heq⟩ :=
      (not_irreducible_iff_projective_solution (map τ F) (hF.map τ) hne).mp hred
    exact ha (hgood K τ hh.1 a (fun i => by simpa only [map_equations] using heq i))

/-- The same principal open preserves geometric integrality, including
nonvanishing and degree three, over every target field. The actual quotient
after its algebraic-closure extension is the one certified to be a domain. -/
theorem exists_geometrically_integral_principal_open
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (ρ : R →+* Ω) (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (hirr : Irreducible (map ρ F)) :
    ∃ s : R, ρ s ≠ 0 ∧
      ∀ (K : Type*) [Field K] (τ : R →+* K), τ s ≠ 0 →
        (map τ F).totalDegree = 3 ∧ Literature.GeometricallyIntegralForm (map τ F) := by
  obtain ⟨s, hs, hgood⟩ := exists_principal_open ρ F hF hirr
  refine ⟨s, hs, ?_⟩
  intro K _ τ hτ
  let α := algebraMap K (AlgebraicClosure K)
  have hbar : Irreducible (map α (map τ F)) := by
    rw [map_map]
    exact hgood (AlgebraicClosure K) (α.comp τ)
      (by simpa only [RingHom.comp_apply] using (map_ne_zero α).mpr hτ)
  have hne : map τ F ≠ 0 := by
    intro hz
    exact hbar.ne_zero (by rw [hz, map_zero])
  refine ⟨(hF.map τ).totalDegree hne, hne, ?_⟩
  exact (Ideal.Quotient.isDomain_iff_prime _).mpr
    ((Ideal.span_singleton_prime hbar.ne_zero).mpr hbar.prime)

end CubicTenVariables.CubicIrreducibilityOpen
