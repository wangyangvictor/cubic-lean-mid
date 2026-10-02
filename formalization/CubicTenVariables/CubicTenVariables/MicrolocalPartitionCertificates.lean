import CubicTenVariables.MicrolocalPartitionCounts
import CubicTenVariables.MicrolocalTableCertificate
import CubicTenVariables.MicrolocalTerminalPrimeCertificate

/-! Prime certificates for the six parts of the same microlocal partition.
Old-layer points use the off-depth certificate; points entering from a
promotion use that table's certificate; the terminal part uses the proved
rational terminal bound. One polynomial height bound and one complete-sum
constant precede every level and every integer frequency. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.MicrolocalPartitionCertificates
open MvPolynomial HessianTheorem11 RationalConeClosure
open ProjectiveMicrolocalData MicrolocalPromotedPartition MicrolocalPartitionCounts
open scoped BigOperators

/-- Uniform polynomially bounded positive exceptional integers for the
actual prime complete sums, on each of the six rational frequency parts. -/
def Certificates {t : ℕ} (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (U : ℕ → Set (Fin 10 → ℚ)) : Prop :=
  ∃ (C : ℝ) (D : ℕ), 1 ≤ C ∧ ∀ (j : Fin 6) (v : Fin 10 → ℤ),
    (fun a => (v a : ℚ)) ∈ part f U j →
    ∃ Δ : ℕ, 1 ≤ Δ ∧
      (∀ H : ℝ, 1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (Δ : ℝ) ≤ C * H^D) ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
        ‖completeCubicSum F p v‖ ≤ C * (p : ℝ)^((11+(j.val : ℝ))/2)

private theorem height_mono {c C : ℝ} {d D Δ : ℕ}
    (hc : 0 ≤ c) (hC : c ≤ C) (hD : d ≤ D) (v : Fin 10 → ℤ)
    (hheight : ∀ H : ℝ, 1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (Δ : ℝ) ≤ c * H^d) :
    ∀ H : ℝ, 1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (Δ : ℝ) ≤ C * H^D := by
  intro H hH hvH
  exact (hheight H hH hvH).trans (mul_le_mul hC (pow_le_pow_right₀ hH hD)
    (pow_nonneg (by linarith) _) (hc.trans hC))

/-- Join the already proved certificates on precisely the same four-table
partition. The origin is excluded by the actual part definition; level zero
and the terminal level are both included. No new literature input occurs. -/
theorem exists_certificates {t : ℕ} (F : MvPolynomial (Fin 10) ℤ)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (N B : ℕ) (hN : 1 ≤ N) (hgeo : Geometry F f)
    (h : TenMicrolocalIncidence.Conclusion F f N B)
    (T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)) :
    Certificates F f (promotionFamily (fun i => (T i).open)) := by
  classical
  choose u G Co Do hCo hzero hoff using fun i : Fin 5 =>
    MicrolocalIntegerCertificate.exists_off_depth_certificate h hN i.val (by omega)
  choose Ct Dt hCt htable using fun i : Fin 4 =>
    MicrolocalTableCertificate.exists_certificate (T i)
  obtain ⟨Cc,Dc,hCc,hterminal⟩ :=
    MicrolocalTerminalPrimeCertificate.exists_terminal_certificate F hhom hAn f N B hN hgeo h
  let C : ℝ := (1+2*(B : ℝ)) + Cc + (∑ i, Co i) + (∑ i, Ct i)
  let D : ℕ := Dc + (∑ i, Do i) + (∑ i, Dt i)
  have hCo0 : ∀ i, 0 ≤ Co i := fun i => le_trans (by norm_num) (hCo i)
  have hCt0 : ∀ i, 0 ≤ Ct i := fun i => le_trans (by norm_num) (hCt i)
  have hCc0 : 0 ≤ Cc := le_trans (by norm_num) hCc
  have hSo : 0 ≤ ∑ i, Co i := Finset.sum_nonneg (fun i _ => hCo0 i)
  have hSt : 0 ≤ ∑ i, Ct i := Finset.sum_nonneg (fun i _ => hCt0 i)
  have hB : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCoC (i : Fin 5) : Co i ≤ C := by
    have hi : Co i ≤ ∑ a, Co a := Finset.single_le_sum (fun a _ => hCo0 a) (Finset.mem_univ i)
    dsimp [C]
    linarith
  have hCtC (i : Fin 4) : Ct i ≤ C := by
    have hi : Ct i ≤ ∑ a, Ct a := Finset.single_le_sum (fun a _ => hCt0 a) (Finset.mem_univ i)
    dsimp [C]
    linarith
  have hCcC : Cc ≤ C := by dsimp [C]; linarith
  have hBC : 1+2*(B : ℝ) ≤ C := by dsimp [C]; linarith
  have hDoD (i : Fin 5) : Do i ≤ D := by
    have hi : Do i ≤ ∑ a, Do a := Finset.single_le_sum (fun a _ => Nat.zero_le (Do a))
      (Finset.mem_univ i)
    dsimp [D]
    omega
  have hDtD (i : Fin 4) : Dt i ≤ D := by
    have hi : Dt i ≤ ∑ a, Dt a := Finset.single_le_sum (fun a _ => Nat.zero_le (Dt a))
      (Finset.mem_univ i)
    dsimp [D]
    omega
  have hDcD : Dc ≤ D := by dsimp [D]; omega
  refine ⟨C,D,hC,?_⟩
  intro j v hv
  have hv0 : v ≠ 0 := by
    intro hz
    apply hv.2
    subst v
    ext a
    simp
  by_cases hj : j.val < 5
  · rw [part_eq_source _ j hj] at hv
    rcases hv.1 with hold | hin
    · let i : Fin 5 := ⟨j.val,hj⟩
      have hout : (fun a => (v a : GeometricField)) ∉
          ProjectiveMicrolocalDepth.depth f (i.val+1) := by
        have hout := hold.1.2
        simp only [filtration,if_neg (by omega : j.val+1 ≠ 0)] at hout
        simpa only [i,rationalPoints,rationalEmbedding,map_intCast] using hout
      obtain ⟨Δ,hΔ,_,hheight,hprime⟩ := hoff i v hv0 hout
      refine ⟨Δ,hΔ,height_mono (hCo0 i) (hCoC i) (hDoD i) v hheight,?_⟩
      intro p _ hp
      exact ((hprime p hp).2).trans (mul_le_mul_of_nonneg_right hBC
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    · have hj4 : j.val < 4 := by
        by_contra hn
        have hjv : j.val = 4 := by omega
        rw [hjv] at hin
        simp only [show 4+1=5 by decide,promotionFamily_five,Set.mem_empty_iff_false] at hin
      let i : Fin 4 := ⟨j.val,hj4⟩
      have hi : (fun a => (v a : ℚ)) ∈ (T i).open := by
        simpa only [show j.val+1=i.val+1 from rfl,promotionFamily_level] using hin
      obtain ⟨Δ,hΔ,hheight,hprime⟩ := htable i v hi
      refine ⟨Δ,hΔ,height_mono (hCt0 i) (hCtC i) (hDtD i) v hheight,?_⟩
      intro p _ hp
      have he : (10+((i.val+1 : ℕ) : ℝ))/2 = (11+(j.val : ℝ))/2 := by
        dsimp [i]
        push_cast
        ring
      have hb := hprime p hp
      rw [he] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right (hCtC i)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · have hjv : j.val = 5 := by omega
    obtain ⟨Δ,hΔ,hheight,hprime⟩ := hterminal v hv0
    refine ⟨Δ,hΔ,height_mono hCc0 hCcC hDcD v hheight,?_⟩
    intro p _ hp
    have he : (11+(j.val : ℝ))/2 = (8 : ℝ) := by rw [hjv]; norm_num
    rw [he]
    exact (hprime p hp).trans (mul_le_mul_of_nonneg_right hCcC
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end CubicTenVariables.MicrolocalPartitionCertificates
