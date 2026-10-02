import CubicTenVariables.PolynomialDivisorBound
import CubicTenVariables.ConeTraceOpenAvoidingLocus

/-! Positive exceptional integers on a finite table of actual principal
opens. All height constants precede the table index and integer frequency.
The input estimates concern the original sums on the literal reductions of
these opens; the output preserves their exponents. No partition, new trace
estimate, or literature premise is asserted here. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.HomogeneousOpenIntegerCertificate

open MvPolynomial PolynomialDivisorBound PolynomialExponentialFamily
open ProjectiveFourierIdentity FiniteFieldTraceCharacter
open scoped BigOperators

def certificate {n : ℕ} (N : ℕ) (h : ParameterPolynomial n) (v : Fin n → ℤ) : ℕ :=
  N * (eval v h).natAbs

theorem certificate_pos {n : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (h : ParameterPolynomial n) (v : Fin n → ℤ) (hv : eval v h ≠ 0) :
    1 ≤ certificate N h v := by
  exact Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (by omega : N ≠ 0) (Int.natAbs_ne_zero.mpr hv))

private theorem cast_eval {n : ℕ} (h : ParameterPolynomial n) (v : Fin n → ℤ)
    (K : Type*) [CommRing K] :
    (eval v h : K) = eval (fun a => (v a : K)) (map (Int.castRingHom K) h) := by
  simpa only [Function.comp_def,Int.coe_castRingHom] using map_eval (Int.castRingHom K) v h

/-- Integer equations remain zero, while avoiding the certificate keeps
the open equation nonzero, over every finite field of that characteristic. -/
theorem reduction_mem {n t : ℕ} (N : ℕ) (G : Fin t → ParameterPolynomial n)
    (h : ParameterPolynomial n) (v : Fin n → ℤ)
    (hG : ∀ a, eval v (G a) = 0) (p : ℕ) (hp : ¬ p ∣ certificate N h v)
    (K : Type*) [Field K] [Fintype K] [CharP K p] :
    ¬ p ∣ N ∧ (fun a => (v a : K)) ∈ parameterPoints G h K := by
  have hpN : ¬ p ∣ N := fun hd => hp (hd.trans (dvd_mul_right _ _))
  have hvp : ¬ p ∣ (eval v h).natAbs := fun hd => hp (hd.trans (dvd_mul_left _ _))
  have hcast : (eval v h : K) ≠ 0 := by
    intro hz
    have hd := (CharP.intCast_eq_zero_iff K p _).mp hz
    exact hvp (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd)
  refine ⟨hpN,(mem_parameterPoints G h K _).mpr ⟨?_,?_⟩⟩
  · intro a
    rw [← cast_eval,hG a,Int.cast_zero]
  · simpa only [cast_eval] using hcast

/-- A positive homogeneous open equation excludes the zero frequency
after reduction, without needing an extra coordinate factor. -/
theorem reduction_ne_zero {n t d : ℕ} (N : ℕ) (G : Fin t → ParameterPolynomial n)
    (h : ParameterPolynomial n) (hh : h.IsHomogeneous d) (hd : 0 < d)
    (v : Fin n → ℤ) (hG : ∀ a, eval v (G a) = 0)
    (p : ℕ) (hp : ¬ p ∣ certificate N h v)
    (K : Type*) [Field K] [Fintype K] [CharP K p] : (fun a => (v a : K)) ≠ 0 := by
  have hmem := (reduction_mem N G h v hG p hp K).2
  have hne := ((mem_parameterPoints G h K _).mp hmem).2
  intro hz
  rw [hz] at hne
  exact hne (eval_origin_zero _ (hh.map _) hd)

/-- One coefficient bound and one degree work for the entire finite
table, including the empty table. -/
theorem exists_uniform_height_bound {n k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (h : Fin k → ParameterPolynomial n) :
    ∃ (C : ℝ) (D : ℕ), 1 ≤ C ∧ ∀ (i : Fin k) (v : Fin n → ℤ) (H : ℝ),
      1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (certificate N (h i) v : ℝ) ≤ C * H^D := by
  classical
  let A : ℝ := 1 + ∑ i : Fin k, coefficientBound (h i)
  let D : ℕ := ∑ i : Fin k, (h i).totalDegree
  have hA : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
      le_trans (by norm_num) (one_le_coefficientBound (h i)))
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨(N : ℝ)*A,D,by nlinarith,?_⟩
  intro i v H hH hv
  have hcoeff : coefficientBound (h i) ≤ A := by
    apply (Finset.single_le_sum (fun a _ =>
      le_trans (by norm_num) (one_le_coefficientBound (h a))) (Finset.mem_univ i)).trans
    dsimp [A]
    linarith
  have hdeg : (h i).totalDegree ≤ D :=
    Finset.single_le_sum (fun a _ => Nat.zero_le (h a).totalDegree) (Finset.mem_univ i)
  calc
    (certificate N (h i) v : ℝ) = (N : ℝ) * |(eval v (h i) : ℝ)| := by
      simp only [certificate,Nat.cast_mul,Nat.cast_natAbs,Int.cast_abs]
    _ ≤ (N : ℝ) * (coefficientBound (h i) * H^(h i).totalDegree) :=
      mul_le_mul_of_nonneg_left (eval_abs_le (h i) H hH v hv) (Nat.cast_nonneg N)
    _ ≤ (N : ℝ) * (A * H^D) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      exact mul_le_mul hcoeff (pow_le_pow_right₀ hH hdeg)
        (pow_nonneg (le_trans (by norm_num) hH) _) (le_trans (by norm_num) hA)
    _ = ((N : ℝ)*A) * H^D := by ring

/-- A supplied literal prime-sum bound on the reductions of a finite
table of opens gives uniform polynomial-height certificates at all its
integer points. The arbitrary real exponent alpha is preserved exactly. -/
theorem exists_certificates {n k : ℕ} (F : ParameterPolynomial n)
    (t : Fin k → ℕ) (G : ∀ i : Fin k, Fin (t i) → ParameterPolynomial n)
    (h : Fin k → ParameterPolynomial n) (N : ℕ) (hN : 1 ≤ N)
    (A : ℝ) (α : Fin k → ℝ)
    (hbound : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
      ∀ (i : Fin k) (v : Fin n → ℤ),
        (fun a => (v a : ZMod p)) ∈ parameterPoints (G i) (h i) (ZMod p) →
        ‖completeCubicSum F p v‖ ≤ A * (p : ℝ)^(α i)) :
    ∃ (C : ℝ) (D : ℕ), 1 ≤ C ∧ ∀ (i : Fin k) (v : Fin n → ℤ),
      (∀ a, eval v (G i a) = 0) → eval v (h i) ≠ 0 →
      ∃ Δ : ℕ, Δ = N * (eval v (h i)).natAbs ∧ 1 ≤ Δ ∧
        (∀ H : ℝ, 1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (Δ : ℝ) ≤ C * H^D) ∧
        ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
          ‖completeCubicSum F p v‖ ≤ A * (p : ℝ)^(α i) := by
  obtain ⟨C,D,hC,hheight⟩ := exists_uniform_height_bound N hN h
  refine ⟨C,D,hC,?_⟩
  intro i v hG hv
  refine ⟨certificate N (h i) v,rfl,certificate_pos N hN (h i) v hv,hheight i v,?_⟩
  intro p _ hp
  obtain ⟨hpN,hmem⟩ := reduction_mem N (G i) (h i) v hG p hp (ZMod p)
  exact hbound p hpN i v hmem

/-- The same concrete certificate simultaneously transfers the supplied
prime-trace-character Fourier bounds over every finite extension. -/
theorem exists_certificates_with_fourier {n k : ℕ} (F : ParameterPolynomial n)
    (t : Fin k → ℕ) (G : ∀ i : Fin k, Fin (t i) → ParameterPolynomial n)
    (h : Fin k → ParameterPolynomial n) (N : ℕ) (hN : 1 ≤ N)
    (A : ℝ) (α β : Fin k → ℝ)
    (hbound : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
      ∀ (i : Fin k) (v : Fin n → ℤ),
        (fun a => (v a : ZMod p)) ∈ parameterPoints (G i) (h i) (ZMod p) →
        ‖completeCubicSum F p v‖ ≤ A * (p : ℝ)^(α i))
    (hfourier : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
      ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 →
      ∀ (K : Type) [Field K] [Fintype K] [CharP K p]
        (i : Fin k) (v : Fin n → K), v ∈ parameterPoints (G i) (h i) K →
        ‖normalizedFourierSum (primeTraceCharacter p K ψ) (map (Int.castRingHom K) F) v‖ ≤
          A * (Fintype.card K : ℝ)^(β i)) :
    ∃ (C : ℝ) (D : ℕ), 1 ≤ C ∧ ∀ (i : Fin k) (v : Fin n → ℤ),
      (∀ a, eval v (G i a) = 0) → eval v (h i) ≠ 0 →
      ∃ Δ : ℕ, Δ = N * (eval v (h i)).natAbs ∧ 1 ≤ Δ ∧
        (∀ H : ℝ, 1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (Δ : ℝ) ≤ C * H^D) ∧
        ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
          ‖completeCubicSum F p v‖ ≤ A * (p : ℝ)^(α i) ∧
          ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 →
          ∀ (K : Type) [Field K] [Fintype K] [CharP K p],
            ‖normalizedFourierSum (primeTraceCharacter p K ψ) (map (Int.castRingHom K) F)
              (fun a => (v a : K))‖ ≤ A * (Fintype.card K : ℝ)^(β i) := by
  obtain ⟨C,D,hC,hcert⟩ := exists_certificates F t G h N hN A α hbound
  refine ⟨C,D,hC,?_⟩
  intro i v hG hv
  obtain ⟨Δ,hΔ,hpos,hheight,hsum⟩ := hcert i v hG hv
  refine ⟨Δ,hΔ,hpos,hheight,?_⟩
  intro p _ hp
  refine ⟨hsum p hp,?_⟩
  intro ψ hψ K _ _ _
  have hp' : ¬ p ∣ certificate N (h i) v := by simpa only [certificate,← hΔ] using hp
  obtain ⟨hpN,hmem⟩ := reduction_mem N (G i) (h i) v hG p hp' K
  exact hfourier p hpN ψ hψ K i _ hmem

/-- Direct adapter for the existing geometric principal-open wrapper.
No geometric or trace property is assumed beyond its actual Conclusion. -/
theorem of_avoiding_locus_table {k : ℕ} (F : ParameterPolynomial 10)
    (t u : Fin k → ℕ)
    (G : ∀ i : Fin k, Fin (t i) → ParameterPolynomial 10)
    (H : ∀ i : Fin k, Fin (u i) → ParameterPolynomial 10)
    (r w : Fin k → ℕ) (h : Fin k → ParameterPolynomial 10) (d : Fin k → ℕ)
    (N A : ℕ) (hN : 1 ≤ N)
    (hdata : ∀ i, ConeTraceOpenAvoidingLocus.Conclusion F (G i) (H i)
      (r i) (w i) (h i) (d i) N A) :
    ∃ (C : ℝ) (D : ℕ), 1 ≤ C ∧ ∀ (i : Fin k) (v : Fin 10 → ℤ),
      (∀ a, eval v (G i a) = 0) → eval v (h i) ≠ 0 →
      ∃ Δ : ℕ, Δ = N * (eval v (h i)).natAbs ∧ 1 ≤ Δ ∧
        (∀ R : ℝ, 1 ≤ R → (∀ a, |(v a : ℝ)| ≤ R) → (Δ : ℝ) ≤ C * R^D) ∧
        ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
          ‖completeCubicSum F p v‖ ≤ (A : ℝ) * (p : ℝ)^((w i : ℝ)/2+1) ∧
          ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 →
          ∀ (K : Type) [Field K] [Fintype K] [CharP K p],
            ‖normalizedFourierSum (primeTraceCharacter p K ψ) (map (Int.castRingHom K) F)
              (fun a => (v a : K))‖ ≤ (A : ℝ) * (Fintype.card K : ℝ)^((w i : ℝ)/2) := by
  apply exists_certificates_with_fourier F t G h N hN (A : ℝ)
    (fun i => (w i : ℝ)/2+1) (fun i => (w i : ℝ)/2)
  · intro p _ hp i v hv
    exact (hdata i).complete_sum_bound p hp v hv
  · intro p _ hp ψ hψ K _ _ _ i v hv
    exact (hdata i).fourier_bound p hp ψ hψ K v hv

end CubicTenVariables.HomogeneousOpenIntegerCertificate
