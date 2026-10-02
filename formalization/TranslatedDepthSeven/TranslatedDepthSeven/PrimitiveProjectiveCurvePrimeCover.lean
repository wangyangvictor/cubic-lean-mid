import TranslatedDepthSeven.PrimitiveProjectiveCurvePrimePackets
import TranslatedDepthSeven.Salberger2023CertificatePrimePool
import TranslatedDepthSeven.CharacteristicPolynomialHeight

/-! Covering primitive projective points by smooth residue packets. The
exception is a proper derivative section; the coefficients are fixed. -/
namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000

/-- The first coordinate and one fixed proper derivative are precisely the
integers that must survive at the prime chosen for a point. -/
def primitiveFirstChartCertificate (P : MvPolynomial (Fin 3) ℤ) (j : Fin 3)
    (x : Fin 3 → ℤ) : ℤ := x 0 * eval x (pderiv j P)

 theorem primitiveFirstChartCertificate_exception_card_le
    {d : ℕ} (hd : 1 ≤ d)
    (P : MvPolynomial (Fin 3) ℤ) (hPhom : P.IsHomogeneous d)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (j : Fin 3) (hproper : pderiv j (P.map (Int.castRingHom ℚ)) ∉
      Ideal.span {P.map (Int.castRingHom ℚ)})
    (S : Finset (Fin 3 → ℤ))
    (hprimitive : ∀ x ∈ S, IsPrimitiveIntVector x)
    (hchart : ∀ x ∈ S, x 0 ≠ 0)
    (hzero : ∀ x ∈ S, eval x P = 0) :
    (S.filter (fun x ↦ primitiveFirstChartCertificate P j x = 0)).card ≤
      2 * (d * (d - 1)) := by
  classical
  let I : Ideal (MvPolynomial (Fin 3) ℚ) := Ideal.span {P.map (Int.castRingHom ℚ)}
  have hI : I.IsPrime := (Ideal.span_singleton_prime hPirred.ne_zero).mpr hPirred.prime
  have hIhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ) := by
    apply Ideal.homogeneous_span
    intro f hf
    have hfP : f = P.map (Int.castRingHom ℚ) := Set.mem_singleton_iff.mp hf
    exact ⟨d, hfP.symm ▸ hPhom.map (Int.castRingHom ℚ)⟩
  have hdegree : HasProjectiveDimensionDegree I 1 d :=
    hasProjectiveDimensionDegree_principal_homogeneous _ (hPhom.map _)
      hPirred.ne_zero (by omega) hI
  apply card_primitiveFirstChart_curve_auxiliary_le I hI hIhom hdegree
    (pderiv j (P.map (Int.castRingHom ℚ))) (hPhom.map _).pderiv hproper _
    (fun x hx ↦ hprimitive x (Finset.mem_filter.mp hx).1)
    (fun x hx ↦ hchart x (Finset.mem_filter.mp hx).1)
  · intro x hx
    rw [mem_affineIdealZeroLocus_iff_le_ker_aeval, Ideal.span_le]
    intro f hf
    have hfP : f = P.map (Int.castRingHom ℚ) := Set.mem_singleton_iff.mp hf
    subst f
    change eval (fun i ↦ (x i : ℚ)) (P.map (Int.castRingHom ℚ)) = 0
    rw [eval_map]
    calc
      _ = (eval x P : ℚ) := (eval₂_comp (Int.castRingHom ℚ) x P).symm
      _ = 0 := by rw [hzero x (Finset.mem_filter.mp hx).1, Int.cast_zero]
  · intro x hx
    obtain ⟨hxS, hxD⟩ := Finset.mem_filter.mp hx
    have hderiv : eval x (pderiv j P) = 0 :=
      (mul_eq_zero.mp hxD).resolve_left (hchart x hxS)
    rw [pderiv_map, eval_map]
    calc
      _ = (eval x (pderiv j P) : ℚ) := (eval₂_comp (Int.castRingHom ℚ) x (pderiv j P)).symm
      _ = 0 := by rw [hderiv, Int.cast_zero]

/-- Finite prime cover, including its literal exceptional locus. -/
theorem card_primitiveFirstChart_le_prime_cover
    {d B : ℕ} (hd : 2 ≤ d) (hB : 1 ≤ B)
    (P : MvPolynomial (Fin 3) ℤ) (hPhom : P.IsHomogeneous d)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (j : Fin 3) (hproper : pderiv j (P.map (Int.castRingHom ℚ)) ∉
      Ideal.span {P.map (Int.castRingHom ℚ)})
    (S : Finset (Fin 3 → ℤ))
    (hprimitive : ∀ x ∈ S, IsPrimitiveIntVector x)
    (hchart : ∀ x ∈ S, x 0 ≠ 0)
    (hzero : ∀ x ∈ S, eval x P = 0)
    (hbox : ∀ x ∈ S, ∀ i, (x i).natAbs ≤ B)
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime ∧ 4 * B < p)
    (havoid : ∀ x ∈ S, primitiveFirstChartCertificate P j x ≠ 0 →
      ∃ p ∈ primes, ¬ (p : ℤ) ∣ primitiveFirstChartCertificate P j x) :
    S.card ≤ 2 * (d * (d - 1)) + ∑ p ∈ primes, (d * p) * (2 * d ^ 2) := by
  classical
  let bad := S.filter (fun x ↦ primitiveFirstChartCertificate P j x = 0)
  let residues := fun p ↦ planeCurveSmoothResidues (planeCurveFirstChartDehomogenize P) p
  let packets := fun p ↦ (residues p).biUnion (primitiveProjectiveFirstPacket p S)
  have hcover : S ⊆ bad ∪ primes.biUnion packets := by
    intro x hx
    by_cases hb : primitiveFirstChartCertificate P j x = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hb⟩)
    obtain ⟨p, hp, hpD⟩ := havoid x hx hb
    letI : Fact p.Prime := ⟨(hprimes p hp).1⟩
    have hDmod : (primitiveFirstChartCertificate P j x : ZMod p) ≠ 0 := by
      intro h
      exact hpD ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
    have hx0 : (x 0 : ZMod p) ≠ 0 := fun h ↦ hDmod (by
      simp only [primitiveFirstChartCertificate, Int.cast_mul, h, zero_mul])
    have hgrad : (eval x (pderiv j P) : ZMod p) ≠ 0 := fun h ↦ hDmod (by
      simp only [primitiveFirstChartCertificate, Int.cast_mul, h, mul_zero])
    have hrho := primitiveProjectiveFirstResidue_mem_smooth (hprimes p hp).1
      P hPhom x (hzero x hx) hx0 j hgrad
    have hpacket : x ∈ primitiveProjectiveFirstPacket p S (primitiveProjectiveFirstResidue p x) := by
      apply Finset.mem_filter.mpr
      refine ⟨hx, hx0, ?_⟩
      intro i
      simp [primitiveProjectiveFirstResidue, ← mul_assoc, hx0]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨p, hp, Finset.mem_biUnion.mpr ⟨_, hrho, hpacket⟩⟩)
  have hcount (p : ℕ) (hp : p ∈ primes) :
      (packets p).card ≤ (d * p) * (2 * d ^ 2) := by
    have hres : (residues p).card ≤ d * p :=
      (card_planeCurveSmoothResidues_le _ (hprimes p hp).1).trans
        (Nat.mul_le_mul_right p ((totalDegree_planeCurveFirstChartDehomogenize_le P).trans hPhom.totalDegree_le))
    calc
      (packets p).card ≤ ∑ rho ∈ residues p, (primitiveProjectiveFirstPacket p S rho).card := Finset.card_biUnion_le
      _ ≤ ∑ _rho ∈ residues p, 2 * d ^ 2 := by
        apply Finset.sum_le_sum
        intro rho hrho
        exact card_primitiveProjectiveFirstPacket_le hd hB (hprimes p hp).1 P hPhom hPirred S
          hprimitive hzero hbox (hprimes p hp).2 rho hrho
      _ = (residues p).card * (2 * d ^ 2) := by simp
      _ ≤ (d * p) * (2 * d ^ 2) := Nat.mul_le_mul_right _ hres
  calc
    S.card ≤ (bad ∪ primes.biUnion packets).card := Finset.card_le_card hcover
    _ ≤ bad.card + (primes.biUnion packets).card := Finset.card_union_le _ _
    _ ≤ bad.card + ∑ p ∈ primes, (packets p).card := Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ 2 * (d * (d - 1)) + ∑ p ∈ primes, (d * p) * (2 * d ^ 2) := by
      apply Nat.add_le_add
      · exact primitiveFirstChartCertificate_exception_card_le (by omega) P hPhom hPirred j hproper S
          hprimitive hchart hzero
      · exact Finset.sum_le_sum hcount

end
end TranslatedDepthSeven
