import CubicTenVariables.BinarySliceGeometry
import CubicTenVariables.BinarySliceLeadingCoefficient
import CubicTenVariables.FiniteFieldPolynomialZeros

/-! A fixed pure cubic coefficient controls the degree of every binary
slice, over every extension of every permitted residue characteristic. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.IntegralBinarySliceDegree
open MvPolynomial BinarySliceCounting BinarySliceGeometry HessianTheorem11
open scoped BigOperators Classical

theorem pure_cubic_coeff_ne_zero {n : ℕ} (F : MvPolynomial (Fin n) ℚ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic F) (i : Fin n) :
    coeff (Finsupp.single i 3) F ≠ 0 := by
  intro hz
  have he : eval (Pi.single i 1) F = 0 := by
    apply MvPolynomial.eval₂Hom_eq_zero
    intro m hm
    have hex : ∃ j ∈ m.support, j ≠ i := by
      by_contra! h
      have hsub : m.support ⊆ {i} := by
        intro j hj
        exact Finset.mem_singleton.mpr (h j hj)
      have hform : m = Finsupp.single i (m i) :=
        Finsupp.support_subset_singleton.mp hsub
      have hdegree : m.degree = 3 := by
        rw [Finsupp.degree_eq_weight_one]
        exact hF hm
      have hdegree' : (Finsupp.single i (m i)).degree = 3 := by
        rw [← hform]
        exact hdegree
      have hmi : m i = 3 := by simpa only [Finsupp.degree_single] using hdegree'
      have hmeq : m = Finsupp.single i 3 := by rwa [hmi] at hform
      exact hm (by simpa only [hmeq] using hz)
    obtain ⟨j,hj,hji⟩ := hex
    exact ⟨j,hj,by simp [hji]⟩
  have hi := congrFun (hA (Pi.single i 1) he) i
  simpa using hi

theorem slice_degree_eq {n d : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) (hF : F.totalDegree ≤ d)
    (e : Fin 2 ↪ Fin n) (j : Fin 2)
    (hc : coeff (Finsupp.single (e j) d) F ≠ 0) (w : Complement e → K) :
    (slice e F w).totalDegree = d := by
  apply le_antisymm ((totalDegree_slice_le e F w).trans hF)
  have hs : coeff (Finsupp.single j d) (slice e F w) ≠ 0 := by
    change coeff (Finsupp.single j d) (aeval _ F) ≠ 0
    rwa [BinarySliceLeadingCoefficient.coeff_pure_slice e F w j hF]
  simpa using le_totalDegree (mem_support_iff.mpr hs)

theorem reduced_slice_degree {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (e : Fin 2 ↪ Fin n) (j : Fin 2)
    (p : ℕ) (hp : ¬ p ∣ (coeff (Finsupp.single (e j) 3) F).natAbs)
    (K : Type*) [Field K] [CharP K p] (w : Complement e → K) :
    (slice e (map (Int.castRingHom K) F) w).totalDegree = 3 := by
  have hc : ((coeff (Finsupp.single (e j) 3) F : ℤ) : K) ≠ 0 := by
    intro hz
    have hd := (CharP.intCast_eq_zero_iff K p _).mp hz
    exact hp (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd)
  apply slice_degree_eq _ ((Finset.sup_mono (support_map_subset _ _)).trans hF.totalDegree_le)
    e j
  simpa only [coeff_map] using hc

/-- Rational anisotropy supplies a nonzero coefficient at any selected
coordinate; one positive integer therefore works for every field and slice. -/
theorem exists_uniform_slice_degree {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (e : Fin 2 ↪ Fin n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : ℕ, ¬ p ∣ N →
      ∀ (K : Type*) [Field K] [CharP K p] (w : Complement e → K),
        (slice e (map (Int.castRingHom K) F) w).totalDegree = 3 := by
  have hcQ := pure_cubic_coeff_ne_zero (map (Int.castRingHom ℚ) F) (hF.map _) hA (e 0)
  have hc : coeff (Finsupp.single (e 0) 3) F ≠ 0 := by
    intro hz
    apply hcQ
    simp only [coeff_map, hz, map_zero]
  exact ⟨(coeff (Finsupp.single (e 0) 3) F).natAbs,
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hc),
    fun p hp K _ _ w => reduced_slice_degree F hF e 0 p hp K w⟩

end CubicTenVariables.IntegralBinarySliceDegree
