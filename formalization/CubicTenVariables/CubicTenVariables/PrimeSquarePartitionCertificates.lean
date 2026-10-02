import CubicTenVariables.PrimeSquareIntegerCertificate
import CubicTenVariables.PrimeSquareZeroBound
import CubicTenVariables.MicrolocalSquarePartition

/-! Common polynomial-height certificates on all seven actual rational
prime-square frequency parts. The six nonzero levels use their next-depth
equations; the origin uses the proved all-prime singular-residue count. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.PrimeSquarePartitionCertificates
open MvPolynomial HessianTheorem11 RationalConeClosure
open ProjectiveMicrolocalData MicrolocalSquarePartition
open scoped BigOperators

def Certificates {t : ℕ} (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) : Prop :=
  ∃ (C : ℝ) (D : ℕ), 1 ≤ C ∧ ∀ (j : Fin 7) (v : Fin 10 → ℤ),
    (fun a => (v a : ℚ)) ∈ part f j →
    ∃ Δ : ℕ, 1 ≤ Δ ∧
      (∀ H : ℝ, 1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (Δ : ℝ) ≤ C * H^D) ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
        ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^(11+j.val)

/-- One C,D works for the whole partition, including its singleton last
part. The origin certificate is the positive integer one. -/
theorem exists_certificates (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (N B : ℕ) (hN : 1 ≤ N) (hgeo : Geometry F f)
    (h : TenMicrolocalIncidence.Conclusion F f N B) : Certificates F f := by
  classical
  choose u G Co Do hCo hzero hoff using fun i : Fin 6 =>
    PrimeSquareIntegerCertificate.exists_off_depth_certificate lit hF h hN i.val (by omega)
  obtain ⟨Cz,hCz,hzeroBound⟩ := PrimeSquareZeroBound.exists_zero_frequency_bound F hF hAn
  let C : ℝ := Cz + ∑ i, Co i
  let D : ℕ := ∑ i, Do i
  have hCo0 : ∀ i, 0 ≤ Co i := fun i => (by norm_num : (0:ℝ)≤1).trans (hCo i)
  have hsum : 0 ≤ ∑ i, Co i := Finset.sum_nonneg (fun i _ => hCo0 i)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCzC : Cz ≤ C := by dsimp [C]; linarith
  have hCoC (i : Fin 6) : Co i ≤ C := by
    have hi : Co i ≤ ∑ a, Co a :=
      Finset.single_le_sum (fun a _ => hCo0 a) (Finset.mem_univ i)
    dsimp [C]
    linarith
  have hDoD (i : Fin 6) : Do i ≤ D :=
    Finset.single_le_sum (fun a _ => Nat.zero_le (Do a)) (Finset.mem_univ i)
  refine ⟨C,D,hC,?_⟩
  intro j v hv
  by_cases hj : j.val < 6
  · have hnq : (fun a => (v a : ℚ)) ≠ 0 := by
      rw [part_of_lt_six j hj] at hv
      exact hv.2
    have hv0 : v ≠ 0 := by
      intro he
      apply hnq
      subst v
      funext a
      simp
    let i : Fin 6 := ⟨j.val,hj⟩
    have hout : (fun a => (v a : GeometricField)) ∉
        ProjectiveMicrolocalDepth.depth f (i.val+1) := by
      by_cases hj5 : j.val < 5
      · rw [part_eq_layer j hj5] at hv
        have he := hv.1.2
        simp only [MicrolocalPromotedPartition.filtration,if_neg (by omega : j.val+1≠0)] at he
        simpa only [i,rationalPoints,rationalEmbedding,map_intCast] using he
      · have he : j.val=5 := by omega
        simpa only [i,he,show 5+1=6 by decide] using
          MicrolocalTerminalPrimeCertificate.integer_not_mem_depth_six F hF hAn f hgeo v hv0
    obtain ⟨Δ,hΔ,_,hheight,hprime⟩ := hoff i v hv0 hout
    refine ⟨Δ,hΔ,?_,?_⟩
    · intro H hH hvH
      exact (hheight H hH hvH).trans
        (mul_le_mul (hCoC i) (pow_le_pow_right₀ hH (hDoD i))
          (pow_nonneg (by linarith) _) (by linarith))
    · intro p _ hp
      exact (hprime p hp).trans
        (mul_le_mul_of_nonneg_right (hCoC i) (by positivity))
  · have hjv : j=⟨6,by decide⟩ := by
      apply Fin.ext
      change j.val=6
      omega
    subst j
    rw [part_six] at hv
    have hv0 : v=0 := by
      have he : (fun a => (v a : ℚ))=0 := hv
      funext a
      have ha : (v a : ℚ)=0 := congrFun he a
      change v a=0
      exact_mod_cast ha
    subst v
    refine ⟨1,by decide,?_,?_⟩
    · intro H hH _
      norm_num only [Nat.cast_one]
      exact (le_mul_of_one_le_right (by linarith : 0≤C)
        (one_le_pow₀ hH)).trans' hC
    · intro p _ _
      exact (hzeroBound p).trans (mul_le_mul_of_nonneg_right hCzC (by positivity))

end CubicTenVariables.PrimeSquarePartitionCertificates
