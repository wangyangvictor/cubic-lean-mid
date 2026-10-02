import Mathlib.Algebra.MvPolynomial.Degrees

/-! One nonzero leading coefficient preserves the actual total degree under
every coefficient specialization on its principal open. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PolynomialDegreePrincipalOpen
open MvPolynomial

/-- An injective coefficient map preserves the literal support and degree. -/
theorem totalDegree_map_of_injective {σ R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (hρ : Function.Injective ρ) (F : MvPolynomial σ R) :
    (map ρ F).totalDegree = F.totalDegree := by
  simp only [totalDegree, support_map_of_injective F hρ]

/-- A single coefficient, chosen before all specializations, preserves a
positive total degree whenever that coefficient remains nonzero. -/
theorem exists_nonzero_coefficient {σ R : Type*} [CommRing R]
    (F : MvPolynomial σ R) {d : ℕ} (hd : 0 < d) (hF : F.totalDegree = d) :
    ∃ c : R, c ≠ 0 ∧
      ∀ (S : Type*) [CommRing S] (ρ : R →+* S), ρ c ≠ 0 →
        (map ρ F).totalDegree = d := by
  classical
  have hF0 : F ≠ 0 := by
    intro h
    simp [h] at hF
    omega
  obtain ⟨m, hm, hdegree⟩ := F.support.exists_mem_eq_sup
    (Finsupp.support_nonempty_iff.mpr hF0) (fun m => m.sum fun _ e => e)
  refine ⟨coeff m F, mem_support_iff.mp hm, ?_⟩
  intro S _ ρ hc
  apply le_antisymm
  · exact (Finset.sup_mono (support_map_subset ρ F)).trans hF.le
  · have hm' : m ∈ (map ρ F).support := mem_support_iff.mpr (by
      simpa only [coeff_map] using hc)
    have hd' : d = m.sum (fun _ e => e) := hF.symm.trans hdegree
    rw [hd']
    exact le_totalDegree hm'

end CubicTenVariables.PolynomialDegreePrincipalOpen
