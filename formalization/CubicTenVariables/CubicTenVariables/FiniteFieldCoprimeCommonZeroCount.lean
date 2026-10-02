import CubicTenVariables.CoprimeCommonZeroCount
import CubicTenVariables.UniformFiniteFieldIdealCount

/-! A uniform common-zero count for relatively prime bounded-degree equations
in every finite field. The constant precedes the field and coefficients;
relative primality and dimension concern the actual field-valued equations. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.FiniteFieldCoprimeCommonZeroCount
open MvPolynomial TranslatedDepthSeven
open scoped BigOperators Classical

private abbrev CoeffIndex (m D : ℕ) := Fin 2 × BoundedDegreeMonomial m D

private def universal (m D : ℕ) (i : Fin 2) :
    MvPolynomial (Fin m) (MvPolynomial (CoeffIndex m D) ℤ) :=
  ∑ s : BoundedDegreeMonomial m D, monomial s.1 (X (i,s))

private theorem specialize_universal {m D : ℕ} {K : Type*} [CommRing K]
    (f : Fin 2 → MvPolynomial (Fin m) K) (hdeg : ∀ i, (f i).totalDegree ≤ D)
    (i : Fin 2) :
    map (eval₂Hom (Int.castRingHom K) (fun t : CoeffIndex m D => (f t.1).coeff t.2.1))
      (universal m D i) = f i := by
  classical
  simp only [universal,map_sum,map_monomial]
  ext s
  simp only [coeff_sum,coeff_monomial]
  by_cases hs : Finsupp.degree s ≤ D
  · let b : BoundedDegreeMonomial m D := ⟨s,hs⟩
    rw [Finset.sum_eq_single b]
    · simp [b]
    · intro t _ htb
      have hne : t.1 ≠ s := fun he => htb (Subtype.ext he)
      simp [hne]
    · simp
  · have hz : (f i).coeff s = 0 := by
      apply notMem_support_iff.mp
      intro hmem
      apply hs
      simpa [Finsupp.degree_eq_sum,Finsupp.sum_fintype] using
        (le_totalDegree hmem).trans (hdeg i)
    rw [hz]
    apply Finset.sum_eq_zero
    intro t _
    have hne : t.1 ≠ s := fun he => hs (he ▸ t.2)
    simp [hne]

/-- One constant precedes every finite field and every relatively prime pair of
polynomials of the displayed bounded degrees.  All finite fields are included. -/
theorem exists_bound (m D : ℕ) (hm : 2 ≤ m) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (K : Type) [Field K] [Fintype K]
      (Q C : MvPolynomial (Fin m) K),
      Q ≠ 0 → Q.totalDegree ≤ D → C.totalDegree ≤ D → IsRelPrime Q C →
      Nat.card {x : Fin m → K // eval x Q=0 ∧ eval x C=0} ≤ A*Nat.card K^(m-2) := by
  classical
  let I := Ideal.span ({universal m D 0,universal m D 1} :
    Set (MvPolynomial (Fin m) (MvPolynomial (CoeffIndex m D) ℤ)))
  obtain ⟨A,hA,hcount⟩ := UniformFiniteFieldIdealCount.exists_bound I
  refine ⟨A,hA,?_⟩
  intro K _ _ Q C hQ hQD hCD hcop
  let f : Fin 2 → MvPolynomial (Fin m) K := ![Q,C]
  let ρ : MvPolynomial (CoeffIndex m D) ℤ →+* K :=
    eval₂Hom (Int.castRingHom K) (fun t => (f t.1).coeff t.2.1)
  have hdeg : ∀ i, (f i).totalDegree ≤ D := by
    intro i
    fin_cases i
    · exact hQD
    · exact hCD
  have hs0 : map ρ (universal m D 0) = Q := specialize_universal f hdeg 0
  have hs1 : map ρ (universal m D 1) = C := specialize_universal f hdeg 1
  have hmap : I.map (map ρ) = Ideal.span {Q,C} := by
    simp only [I,Ideal.map_span,Set.image_insert_eq,Set.image_singleton,hs0,hs1]
  have hdim : ringKrullDim (MvPolynomial (Fin m) K ⧸ I.map (map ρ)) ≤
      ((m-2 : ℕ) : WithBot ℕ∞) := by
    rw [hmap]
    exact CoprimeCommonZeroCount.quotient_dimension_le hm Q C hQ hcop
  have hz (x : Fin m → K) :
      (∀ P ∈ I, eval₂Hom ρ x P=0) ↔ eval x Q=0 ∧ eval x C=0 := by
    have h0 : eval₂Hom ρ x (universal m D 0) = eval x Q := by
      rw [← hs0,eval_map]; rfl
    have h1 : eval₂Hom ρ x (universal m D 1) = eval x C := by
      rw [← hs1,eval_map]; rfl
    constructor
    · intro hx
      exact ⟨h0 ▸ hx _ (Ideal.subset_span (by simp)),
        h1 ▸ hx _ (Ideal.subset_span (by simp))⟩
    · rintro ⟨hq,hc⟩ P hP
      have hle : I ≤ RingHom.ker (eval₂Hom ρ x) := by
        apply Ideal.span_le.mpr
        intro V hV
        rcases hV with rfl | hV
        · exact h0.trans hq
        · rw [Set.mem_singleton_iff] at hV
          subst V
          exact h1.trans hc
      exact hle hP
  rw [← Nat.card_congr (Equiv.subtypeEquivRight hz)]
  exact hcount K ρ (m-2) hdim

/-- The quadratic/cubic intersection estimate used after projection from
a rational double point. -/
theorem exists_quadratic_cubic_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (K : Type) [Field K] [Fintype K]
      (Q C : MvPolynomial (Fin m) K),
      Q ≠ 0 → Q.totalDegree ≤ 2 → C.totalDegree ≤ 3 → IsRelPrime Q C →
      Nat.card {x : Fin m → K // eval x Q=0 ∧ eval x C=0} ≤ A*Nat.card K^(m-2) := by
  obtain ⟨A,hA,h⟩ := exists_bound m 3 hm
  exact ⟨A,hA,fun K _ _ Q C hQ hQD hCD hcop =>
    h K Q C hQ (hQD.trans (by decide)) hCD hcop⟩

end CubicTenVariables.FiniteFieldCoprimeCommonZeroCount
