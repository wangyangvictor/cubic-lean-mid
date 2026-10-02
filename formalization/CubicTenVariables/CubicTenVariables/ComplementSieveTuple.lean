import CubicTenVariables.OriginAdjoinedDepthModels
import CubicTenVariables.NumericalDepthAllocation
import CubicTenVariables.GeometricConeSieve
import CubicTenVariables.StratifiedSieveData

/-! Actual numerical-depth factors satisfy the integral-model conditions of
the stratified sieve. Depths are evaluated at the original integer vector;
no periodicity assertion is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.ComplementSieveTuple
open MvPolynomial NumericalPrimeDepth NumericalDepthAllocation OriginAdjoinedDepthModels

variable {t N : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
  {C : ℝ} {d : ℕ} {h : CoarseBounds F C}

private theorem merged_dvd (a b : ℕ) (v : Fin 10 → ℤ) (j : ℕ) :
    mergedPart h a b v j ∣ a*b^2 := by
  have hd := Nat.mul_dvd_mul (parts_dvd h a b v j).1 (parts_dvd h a b v j).2
  exact hd.trans (Nat.mul_dvd_mul_left a (by rw [pow_two]; exact dvd_mul_right b b))

private theorem depth_of_prime_dvd (a b : ℕ) (v : Fin 10 → ℤ) (j p : ℕ)
    (hp : p.Prime) (hd : p ∣ mergedPart h a b v j) :
    NumericalConductor.primeDepth h p v = j ∨ NumericalConductor.squareDepth h p v = j := by
  rcases hp.dvd_mul.mp hd with hd | hd
  · left
    have hm := hp.mem_primeFactors hd (parts_pos h a b v j).1.ne'
    rw [(parts_primeFactors h a b v j).1] at hm
    exact (Finset.mem_filter.mp hm).2
  · right
    have hm := hp.mem_primeFactors hd (parts_pos h a b v j).2.ne'
    rw [(parts_primeFactors h a b v j).2] at hm
    exact (Finset.mem_filter.mp hm).2

private theorem squarefree_dvd_integer (q : ℕ) (hq : Squarefree q) (z : ℤ)
    (hz : ∀ p ∈ q.primeFactors, (p : ℤ) ∣ z) : (q : ℤ) ∣ z := by
  by_cases hzero : z=0
  · simp [hzero]
  apply Int.natCast_dvd.mpr
  rw [← Nat.prod_primeFactors_of_squarefree hq]
  apply dvd_trans _ (Nat.prod_primeFactors_dvd z.natAbs)
  apply Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p)
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).mem_primeFactors
    (Int.natCast_dvd.mp (hz p hp)) (Int.natAbs_ne_zero.mpr hzero)

/-- Every polynomial of the actual support ideal vanishes modulo its
merged depth factor. Squarefreeness is proved from the original factors. -/
theorem ideal_divisibility (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (M : ∀ j : Fin 5, Model f N j) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (hN : (a*b^2).Coprime N) (v : Fin 10 → ℤ) (j : Fin 5) :
    ∀ P ∈ Ideal.span (Set.range (M j).equations),
      (mergedPart h a b v (j.val+2) : ℤ) ∣ eval v P := by
  intro P hP
  apply squarefree_dvd_integer _ (merged_squarefree h a b ha hb hab v _) _
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  letI : Fact p.Prime := ⟨hpprime⟩
  have hpdvd := Nat.dvd_of_mem_primeFactors hp
  have hpN : ¬ p ∣ N := hpprime.coprime_iff_not_dvd.mp
    (Nat.Coprime.of_dvd_left (hpdvd.trans (merged_dvd a b v _)) hN)
  have hdepth := depth_of_prime_dvd a b v (j.val+2) p hpprime hpdvd
  simp only [NumericalConductor.primeDepth_of_prime,
    NumericalConductor.squareDepth_of_prime] at hdepth
  have hgens := (M j).modular_vanishing hc p hpN v
    (hdepth.elim (fun he => Or.inl (le_of_eq he.symm))
      (fun he => Or.inr (le_of_eq he.symm)))
  have he := (IntegralConeNormalization.forall_eval_span_iff (M j).equations
    (fun k => (v k : ZMod p))).mpr hgens P hP
  rw [GeometricConeSieve.int_eval_cast] at he
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he

/-- Any injectively selected deeper levels form a literal valid sieve
 tuple, with the stated spatial, progression and dyadic conditions. -/
theorem validTuple {s : ℕ}
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (M : ∀ j : Fin 5, Model f N j) (i : Fin 5)
    (e : Fin s → Fin 5) (he : Function.Injective e)
    (hei : ∀ k, i.val ≤ (e k).val)
    (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (hN : (a*b^2).Coprime N) (m : ℕ) (hm : m.Coprime (a*b^2))
    (u : Fin 10 → ℝ) (L : ℝ) (v₀ v : Fin 10 → ℤ) (R : Fin s → ℝ)
    (hv : (fun k => (v k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i)
    (hbox : ∀ k, |(v k : ℝ)-u k| ≤ L)
    (hprog : ∀ k, (m : ℤ) ∣ v k-v₀ k)
    (hdyadic : ∀ k, R k ≤ (mergedPart h a b v ((e k).val+2) : ℝ) ∧
      (mergedPart h a b v ((e k).val+2) : ℝ) ≤ 2*R k) :
    StratifiedSieveData.ValidTuple (fun k => (M (e k)).count)
      (fun k => (M (e k)).equations)
      {v | (fun k => (v k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i}
      u L m v₀ R (fun k => mergedPart h a b v ((e k).val+2), v) := by
  refine ⟨fun k => merged_squarefree h a b ha hb hab v _, ?_, ?_, hv, hbox, hprog,
    ?_, ?_, hdyadic⟩
  · intro k l hkl
    apply merged_coprime h a b hab v
    intro hlevel
    apply hkl
    apply he
    apply Fin.ext
    omega
  · intro k
    exact Nat.Coprime.of_dvd_right (merged_dvd a b v _) hm
  · intro k
    obtain ⟨z,hz⟩ := (M (e k)).outside_piece tables i (hei k) v hv
    exact ⟨(M (e k)).equations z, Ideal.subset_span (Set.mem_range_self z), hz⟩
  · intro k
    exact ideal_divisibility hc M a b ha hb hab hN v (e k)

/-- The increasing index of all depth supports from i+2 through six. -/
def tailIndex (i : Fin 5) (k : Fin (5-i.val)) : Fin 5 := ⟨i.val+k.val, by omega⟩

theorem tailIndex_injective (i : Fin 5) : Function.Injective (tailIndex i) := by
  intro k l hkl
  have he := congrArg Fin.val hkl
  apply Fin.ext
  simp only [tailIndex] at he
  omega

/-- The exact full tail, without omitted depth levels, satisfies the sieve. -/
theorem tail_validTuple
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (M : ∀ j : Fin 5, Model f N j) (i : Fin 5)
    (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (hN : (a*b^2).Coprime N) (m : ℕ) (hm : m.Coprime (a*b^2))
    (u : Fin 10 → ℝ) (L : ℝ) (v₀ v : Fin 10 → ℤ) (R : Fin (5-i.val) → ℝ)
    (hv : (fun k => (v k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i)
    (hbox : ∀ k, |(v k : ℝ)-u k| ≤ L)
    (hprog : ∀ k, (m : ℤ) ∣ v k-v₀ k)
    (hdyadic : ∀ k, R k ≤ (mergedPart h a b v ((tailIndex i k).val+2) : ℝ) ∧
      (mergedPart h a b v ((tailIndex i k).val+2) : ℝ) ≤ 2*R k) :
    StratifiedSieveData.ValidTuple (fun k => (M (tailIndex i k)).count)
      (fun k => (M (tailIndex i k)).equations)
      {v | (fun k => (v k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i}
      u L m v₀ R (fun k => mergedPart h a b v ((tailIndex i k).val+2), v) :=
  validTuple hc M i (tailIndex i) (tailIndex_injective i) (fun k => by
    simp only [tailIndex]; omega) a b ha hb hab hN m hm u L v₀ v R hv hbox hprog hdyadic

end CubicTenVariables.ComplementSieveTuple
