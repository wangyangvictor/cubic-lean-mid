import CubicTenVariables.MicrolocalOffDepthBound

/-! Concrete exceptional integers for a nonzero integral frequency outside
a fixed finite family of equations. The integer contains the already fixed
bad-prime factor, one nonzero equation value and one nonzero coordinate.
Its polynomial height bound is uniform in all choices of these two indices.
There is no new literature premise. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.MicrolocalIntegerCertificate

open MvPolynomial HessianTheorem11 PolynomialDivisorBound
open scoped BigOperators

def certificate {n u : ℕ} (N : ℕ) (G : Fin u → MvPolynomial (Fin n) ℤ)
    (i : Fin u) (k : Fin n) (v : Fin n → ℤ) : ℕ :=
  N * (eval v (G i) * v k).natAbs

theorem certificate_pos {n u : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (G : Fin u → MvPolynomial (Fin n) ℤ) (i : Fin u) (k : Fin n)
    (v : Fin n → ℤ) (hi : eval v (G i) ≠ 0) (hk : v k ≠ 0) :
    1 ≤ certificate N G i k v := by
  unfold certificate
  have hp : 0 < (eval v (G i) * v k).natAbs :=
    Int.natAbs_pos.mpr (mul_ne_zero hi hk)
  exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))

private theorem cast_eval {n : ℕ} (P : MvPolynomial (Fin n) ℤ)
    (v : Fin n → ℤ) (K : Type*) [CommRing K] :
    (eval v P : K) = eval₂ (Int.castRingHom K) (fun i => (v i : K)) P := by
  simpa only [Function.comp_def,Int.coe_castRingHom,eval₂_eq_eval_map] using
    map_eval (Int.castRingHom K) v P

/-- Avoiding this one integer simultaneously avoids the fixed bad primes,
the zero frequency and the common zero set, over every field of that
characteristic. No assumption that the field is prime or finite is needed. -/
theorem good_reduction {n u : ℕ} (N : ℕ)
    (G : Fin u → MvPolynomial (Fin n) ℤ) (i : Fin u) (k : Fin n)
    (v : Fin n → ℤ) (p : ℕ) (hp : ¬ p ∣ certificate N G i k v)
    (K : Type*) [Field K] [CharP K p] :
    ¬ p ∣ N ∧ (fun a => (v a : K)) ≠ 0 ∧
      eval₂ (Int.castRingHom K) (fun a => (v a : K)) (G i) ≠ 0 := by
  have hpN : ¬ p ∣ N := fun hd => hp (hd.trans (dvd_mul_right _ _))
  have hprod : ¬ p ∣ (eval v (G i) * v k).natAbs :=
    fun hd => hp (hd.trans (dvd_mul_left _ _))
  have hcast : ((eval v (G i) * v k : ℤ) : K) ≠ 0 := by
    intro hz
    have hd := (CharP.intCast_eq_zero_iff K p _).mp hz
    exact hprod (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd)
  have he : (eval v (G i) : K) ≠ 0 := by
    intro hz
    apply hcast
    simp only [Int.cast_mul,hz,zero_mul]
  have hk : (v k : K) ≠ 0 := by
    intro hz
    apply hcast
    simp only [Int.cast_mul,hz,mul_zero]
  refine ⟨hpN,?_,?_⟩
  · intro hz
    exact hk (congrFun hz k)
  · simpa only [cast_eval] using he

/-- Uniform polynomial growth for every possible chosen equation and
coordinate. C and D depend only on the fixed integer N and finite family. -/
theorem exists_uniform_height_bound {n u : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (G : Fin u → MvPolynomial (Fin n) ℤ) :
    ∃ (C : ℝ) (D : ℕ), 1 ≤ C ∧ ∀ (i : Fin u) (k : Fin n)
      (v : Fin n → ℤ) (H : ℝ), 1 ≤ H →
      (∀ a, |(v a : ℝ)| ≤ H) → (certificate N G i k v : ℝ) ≤ C * H^D := by
  classical
  let A : ℝ := 1 + ∑ i : Fin u, coefficientBound (G i)
  let D : ℕ := (∑ i : Fin u, (G i).totalDegree) + 1
  have hA : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
      le_trans (by norm_num) (one_le_coefficientBound (G i)))
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨(N : ℝ)*A,D,by nlinarith,?_⟩
  intro i k v H hH hv
  have hcoeff : coefficientBound (G i) ≤ A := by
    apply (Finset.single_le_sum (fun a _ =>
      le_trans (by norm_num) (one_le_coefficientBound (G a))) (Finset.mem_univ i)).trans
    dsimp [A]
    linarith
  have hdeg : (G i).totalDegree + 1 ≤ D := by
    dsimp [D]
    exact Nat.add_le_add_right
      (Finset.single_le_sum (fun a _ => Nat.zero_le (G a).totalDegree) (Finset.mem_univ i)) 1
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  calc
    (certificate N G i k v : ℝ) =
        (N : ℝ) * (|(eval v (G i) : ℝ)| * |(v k : ℝ)|) := by
      simp only [certificate,Nat.cast_mul,Nat.cast_natAbs,Int.cast_abs,Int.cast_mul,abs_mul]
    _ ≤ (N : ℝ) * (coefficientBound (G i) * H^(G i).totalDegree * H) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      exact mul_le_mul (eval_abs_le (G i) H hH v hv) (hv k)
        (abs_nonneg _) (mul_nonneg (le_trans (by norm_num) (one_le_coefficientBound _))
          (pow_nonneg hH0 _))
    _ = ((N : ℝ)*coefficientBound (G i)) * H^((G i).totalDegree+1) := by
      rw [pow_succ]
      ring
    _ ≤ ((N : ℝ)*A) * H^D := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg N))
        (pow_le_pow_right₀ hH hdeg) (pow_nonneg hH0 _)
        (mul_nonneg (Nat.cast_nonneg N) (le_trans (by norm_num) hA))

/-- A positive exceptional integer with a uniform polynomial bound can
be chosen at every nonzero integral point outside the actual common zeros. -/
theorem exists_bounded_certificate {n u : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (G : Fin u → MvPolynomial (Fin n) ℤ) :
    ∃ (C : ℝ) (D : ℕ), 1 ≤ C ∧ ∀ v : Fin n → ℤ, v ≠ 0 →
      (∃ i, eval v (G i) ≠ 0) →
      ∃ Δ : ℕ, 1 ≤ Δ ∧
        (∃ (i : Fin u) (k : Fin n), eval v (G i) ≠ 0 ∧ v k ≠ 0 ∧
          Δ = N * (eval v (G i) * v k).natAbs) ∧
        (∀ H : ℝ, 1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (Δ : ℝ) ≤ C * H^D) ∧
        ∀ p : ℕ, ¬ p ∣ Δ → ∀ (K : Type*) [Field K] [CharP K p],
          ¬ p ∣ N ∧ (fun a => (v a : K)) ≠ 0 ∧
            ∃ i, eval₂ (Int.castRingHom K) (fun a => (v a : K)) (G i) ≠ 0 := by
  obtain ⟨C,D,hC,hbound⟩ := exists_uniform_height_bound N hN G
  refine ⟨C,D,hC,?_⟩
  intro v hv hG
  obtain ⟨i,hi⟩ := hG
  have hk : ∃ k, v k ≠ 0 := by
    by_contra! hz
    exact hv (funext hz)
  obtain ⟨k,hk⟩ := hk
  refine ⟨certificate N G i k v,certificate_pos N hN G i k v hi hk,
    ⟨i,k,hi,hk,rfl⟩,hbound i k v,?_⟩
  intro p hp K _ _
  obtain ⟨hpN,hvK,hiK⟩ := good_reduction N G i k v p hp K
  exact ⟨hpN,hvK,⟨i,hiK⟩⟩

/-- Actual off-depth frequency certificates. The finite equations and
height constants are fixed before v. For every prime outside the resulting
positive integer, the reduction is nonzero and the original T and S sums
have the sharper exponents. This includes j=0. -/
theorem exists_off_depth_certificate {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10} {N B : ℕ}
    (h : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N)
    (j : ℕ) (hj : j ≤ 8) :
    ∃ (u : ℕ) (G : Fin u → MvPolynomial (Fin 10) ℤ) (C : ℝ) (D : ℕ),
      1 ≤ C ∧
      (∀ x : GeometricPoint 10, (∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0) ↔
        x ∈ ProjectiveMicrolocalDepth.depth f (j+1)) ∧
      ∀ v : Fin 10 → ℤ, v ≠ 0 →
        (fun a => (v a : GeometricField)) ∉ ProjectiveMicrolocalDepth.depth f (j+1) →
        ∃ Δ : ℕ, 1 ≤ Δ ∧
          (∃ (i : Fin u) (k : Fin 10), eval v (G i) ≠ 0 ∧ v k ≠ 0 ∧
            Δ = N * (eval v (G i) * v k).natAbs) ∧
          (∀ H : ℝ, 1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (Δ : ℝ) ≤ C * H^D) ∧
          ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
            (∀ (K : Type) [Field K] [Fintype K] [CharP K p]
              (ψ : AddChar K ℂ), ψ ≠ 1 →
              ‖ProjectiveFourierIdentity.normalizedFourierSum ψ (map (Int.castRingHom K) F)
                (fun a => (v a : K))‖ ≤
                (1+2*(B : ℝ)) * (Fintype.card K : ℝ)^((9+(j : ℝ))/2)) ∧
            ‖completeCubicSum F p v‖ ≤ (1+2*(B : ℝ)) * (p : ℝ)^((11+(j : ℝ))/2) := by
  obtain ⟨u,G,d,hd,hI,hgeo,hgood⟩ :=
    MicrolocalOffDepthBound.exists_off_depth_equations h j hj
  obtain ⟨C,D,hC,hcert⟩ := exists_bounded_certificate N hN G
  refine ⟨u,G,C,D,hC,hgeo,?_⟩
  intro v hv hoff
  have hG : ∃ i, eval v (G i) ≠ 0 := by
    by_contra! hz
    apply hoff
    apply (hgeo _).mp
    intro i
    rw [← cast_eval, hz i, Int.cast_zero]
  obtain ⟨Δ,hΔ,heq,hgrowth,hreduce⟩ := hcert v hv hG
  refine ⟨Δ,hΔ,heq,hgrowth,?_⟩
  intro p _ hp
  obtain ⟨hpN,hvp,hGp⟩ := hreduce p hp (ZMod p)
  constructor
  · intro K _ _ _ ψ hψ
    obtain ⟨_,hvK,hGK⟩ := hreduce p hp K
    exact ((hgood p hpN).1 K).2 ψ hψ _ hvK hGK
  · exact (hgood p hpN).2 v hvp hGp

end CubicTenVariables.MicrolocalIntegerCertificate
