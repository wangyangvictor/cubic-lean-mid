import CubicTenVariables.UniversalHomogeneousCombinations
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Funext

/-! A homogeneous equation family whose common zeros are only the origin
at one algebraically closed specialization has the same property on a
principal open of the original coefficient ring. The specialization need
not be injective, and the coefficient ring need not be Noetherian. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.HomogeneousOriginOpen
open MvPolynomial HomogeneousMacaulayCertificates UniversalHomogeneousCombinations

variable {R : Type*} [CommRing R] {n : ℕ} {ι : Type*} [Fintype ι]

/-- Nullstellensatz turns the literal origin-only condition into a finite
homogeneous coordinate quotient, including a possibly empty zero locus. -/
theorem finite_quotient_of_zero_only
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (f : ι → MvPolynomial (Fin n) Ω) (d : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (d j))
    (horigin : ∀ x : Fin n → Ω, (∀ j, eval x (f j) = 0) → x = 0) :
    Module.Finite Ω (MvPolynomial (Fin n) Ω ⧸ Ideal.span (Set.range f)) := by
  classical
  let I := Ideal.span (Set.range f)
  have hpow : ∀ i : Fin n, ∃ k : ℕ, X i ^ k ∈ I := by
    intro i
    apply (Ideal.mem_radical_iff).mp
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := Ω) I]
    intro x hx
    have hx0 : x = 0 := horigin x (fun j => hx (f j) (Ideal.subset_span ⟨j, rfl⟩))
    change eval x (X i) = 0
    rw [eval_X, hx0]
    rfl
  choose k hk using hpow
  obtain ⟨c, hc, _, _⟩ := common_degree_certificates f d hf k hk
  exact finite_quotient_of_certificates f (commonDegree k) (commonDegree_pos k) c hc

/-- A coefficient of the actual universal determinant remains nonzero at
the supplied specialization. Its nonvanishing preserves finiteness and the
origin-only property over every infinite target field. -/
theorem exists_principal_open_of_finite_quotient
    {Ω : Type*} [Field Ω]
    (ρ : R →+* Ω) (f : ι → MvPolynomial (Fin n) R) (d : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (d j))
    [Module.Finite Ω (MvPolynomial (Fin n) Ω ⧸
      Ideal.span (Set.range (fun j => map ρ (f j))))] :
    ∃ s : R, ρ s ≠ 0 ∧
      ∀ (K : Type*) [Field K] [Infinite K] (τ : R →+* K), τ s ≠ 0 →
        Module.Finite K (MvPolynomial (Fin n) K ⧸
          Ideal.span (Set.range (fun j => map τ (f j)))) ∧
        ∀ x : Fin n → K, (∀ j, eval x (map τ (f j)) = 0) → x = 0 := by
  classical
  obtain ⟨N, hN, a, ha⟩ := exists_determinant_of_finite_quotient ρ f d hf
  let P := determinant f d N
  have hP : map ρ P ≠ 0 := by
    intro hzero
    have he : eval a (map ρ P) = 1 := by
      simpa only [← eval₂_eq_eval_map, P] using ha
    rw [hzero, map_zero] at he
    exact zero_ne_one he
  obtain ⟨u, hu⟩ : ∃ u, ρ (coeff u P) ≠ 0 := by
    by_contra! h
    apply hP
    ext u
    simpa only [coeff_map, coeff_zero] using h u
  refine ⟨coeff u P, hu, ?_⟩
  intro K _ _ τ hs
  have hPτ : map τ P ≠ 0 := by
    intro hz
    exact hs (by simpa only [coeff_map, coeff_zero] using congrArg (coeff u) hz)
  obtain ⟨b, hb⟩ : ∃ b, eval b (map τ P) ≠ 0 := by
    by_contra! h
    exact hPτ (MvPolynomial.funext (fun b => by simpa only [map_zero] using h b))
  have hdet : eval₂Hom τ b (determinant f d N) ≠ 0 := by
    simpa only [← eval₂_eq_eval_map, P] using hb
  letI : Module.Finite K (MvPolynomial (Fin n) K ⧸
      Ideal.span (Set.range (fun j => map τ (f j)))) :=
    finite_quotient_of_determinant_ne_zero τ f d hf hN b hdet
  refine ⟨inferInstance, ?_⟩
  obtain ⟨M, _, c, hc, _, _⟩ := exists_common_degree_certificates
    (fun j => map τ (f j)) d (fun j => (hf j).map τ)
  exact zero_of_certificates _ M c hc

/-- Origin-only common zeros persist on one principal open through an
arbitrary good specialization. All fields and maps occur after the single
coefficient s is chosen. No characteristic or Noetherian hypothesis appears. -/
theorem exists_principal_open
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (ρ : R →+* Ω) (f : ι → MvPolynomial (Fin n) R) (d : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (d j))
    (horigin : ∀ x : Fin n → Ω, (∀ j, eval x (map ρ (f j)) = 0) → x = 0) :
    ∃ s : R, ρ s ≠ 0 ∧
      ∀ (K : Type*) [Field K] [IsAlgClosed K] (τ : R →+* K), τ s ≠ 0 →
        ∀ x : Fin n → K, (∀ j, eval x (map τ (f j)) = 0) → x = 0 := by
  letI : Module.Finite Ω (MvPolynomial (Fin n) Ω ⧸
      Ideal.span (Set.range (fun j => map ρ (f j)))) :=
    finite_quotient_of_zero_only (fun j => map ρ (f j)) d (fun j => (hf j).map ρ) horigin
  obtain ⟨s, hs, hgood⟩ := exists_principal_open_of_finite_quotient ρ f d hf
  exact ⟨s, hs, fun K _ _ τ hτ => (hgood K τ hτ).2⟩

end CubicTenVariables.HomogeneousOriginOpen
