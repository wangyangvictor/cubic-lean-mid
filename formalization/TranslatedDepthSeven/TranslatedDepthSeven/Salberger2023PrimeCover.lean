import TranslatedDepthSeven.ComparablePrimePoolBridge
import TranslatedDepthSeven.FiniteResiduePacket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The prime-cover step in Salberger's high-degree curve estimate

The integer certificate is literal.  A product of distinct primes larger
than its absolute value supplies a prime at which it is nonzero.  The
resulting residue packets cover all points outside the certificate's zero
locus.  No assertion that the two original cutting equations have a nonzero
Jacobian minor is included: for a nonreduced or tangent intersection that
assertion needs a separate argument using equations of the reduced curve.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators
open Filter

/-- Every nonzero integer smaller than a squarefree prime product has a
prime in that product which does not divide it. -/
theorem exists_prime_not_dvd_of_natAbs_lt_primeProduct
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ℤ) (hD : D ≠ 0) (hsize : D.natAbs < primeProduct P) :
    ∃ p ∈ P, ¬ (p : ℤ) ∣ D := by
  by_contra! h
  have hdiv : primeProduct P ∣ D.natAbs :=
    primeProduct_dvd_of_each_dvd hP (Finset.Subset.refl P)
      (fun p hp ↦ Int.natCast_dvd.mp (h p hp))
  exact (not_lt_of_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr hD) hdiv)) hsize

/-- Explicit finite prime-cover count.  At each prime, `R p` is a finite
list of good reductions; each corresponding literal residue packet has
at most `packetBound p` points.  The zero locus of the certificate is
retained as an exceptional term. -/
theorem card_le_exceptional_add_prime_residue_packets_of_avoidance
    {N : ℕ} (S : Finset (IntVector N)) (D : IntVector N → ℤ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (R : ∀ p : ℕ, Finset (Fin N → ZMod p))
    (packetBound : ℕ → ℕ)
    (havoidance : ∀ z ∈ S, D z ≠ 0 → ∃ p ∈ P, ¬ (p : ℤ) ∣ D z)
    (hgood : ∀ p ∈ P, ∀ z ∈ S, ¬ (p : ℤ) ∣ D z →
      integralResidueVector z ∈ R p)
    (hpacket : ∀ p ∈ P, ∀ rho ∈ R p,
      (integralResiduePacket S rho).card ≤ packetBound p) :
    S.card ≤ (S.filter (fun z ↦ D z = 0)).card +
      ∑ p ∈ P, (R p).card * packetBound p := by
  classical
  let exceptional := S.filter (fun z ↦ D z = 0)
  let packets := fun p ↦ (R p).biUnion (integralResiduePacket S)
  have hcover : S ⊆ exceptional ∪ P.biUnion packets := by
    intro z hz
    by_cases hzero : D z = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hzero⟩)
    · obtain ⟨p, hp, havoid⟩ := havoidance z hz hzero
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p, hp, Finset.mem_biUnion.mpr
          ⟨integralResidueVector z, hgood p hp z hz havoid,
            mem_integralResiduePacket_iff.mpr ⟨hz, rfl⟩⟩⟩)
  have hpacketSum : ∀ p ∈ P, (packets p).card ≤
      (R p).card * packetBound p := by
    intro p hp
    calc
      (packets p).card ≤ ∑ rho ∈ R p,
          (integralResiduePacket S rho).card := Finset.card_biUnion_le
      _ ≤ ∑ _rho ∈ R p, packetBound p :=
        Finset.sum_le_sum (hpacket p hp)
      _ = (R p).card * packetBound p := by simp
  calc
    S.card ≤ (exceptional ∪ P.biUnion packets).card := Finset.card_le_card hcover
    _ ≤ exceptional.card + (P.biUnion packets).card := Finset.card_union_le _ _
    _ ≤ exceptional.card + ∑ p ∈ P, (packets p).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ exceptional.card + ∑ p ∈ P, (R p).card * packetBound p :=
      Nat.add_le_add_left (Finset.sum_le_sum hpacketSum) _

/-- Prime-product form of the preceding finite cover theorem. -/
theorem card_le_exceptional_add_prime_residue_packets
    {N : ℕ} (S : Finset (IntVector N)) (D : IntVector N → ℤ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (R : ∀ p : ℕ, Finset (Fin N → ZMod p))
    (packetBound : ℕ → ℕ)
    (hsize : ∀ z ∈ S, D z ≠ 0 → (D z).natAbs < primeProduct P)
    (hgood : ∀ p ∈ P, ∀ z ∈ S, ¬ (p : ℤ) ∣ D z →
      integralResidueVector z ∈ R p)
    (hpacket : ∀ p ∈ P, ∀ rho ∈ R p,
      (integralResiduePacket S rho).card ≤ packetBound p) :
    S.card ≤ (S.filter (fun z ↦ D z = 0)).card +
      ∑ p ∈ P, (R p).card * packetBound p :=
  card_le_exceptional_add_prime_residue_packets_of_avoidance S D P hP R
    packetBound (fun z hz hD ↦
      exists_prime_not_dvd_of_natAbs_lt_primeProduct P hP (D z) hD
        (hsize z hz hD)) hgood hpacket

/-- The numerical global count after every good residue packet has the
local curve bound `δ²`.  The prime interval and finite-field point count
enter only through the literal inequalities displayed here. -/
theorem card_le_of_prime_residue_curve_bounds
    {N : ℕ} (S : Finset (IntVector N)) (D : IntVector N → ℤ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (R : ∀ p : ℕ, Finset (Fin N → ZMod p))
    (δ exceptionalBound primeCap residueFactor : ℕ)
    (hsize : ∀ z ∈ S, D z ≠ 0 → (D z).natAbs < primeProduct P)
    (hgood : ∀ p ∈ P, ∀ z ∈ S, ¬ (p : ℤ) ∣ D z →
      integralResidueVector z ∈ R p)
    (hpacket : ∀ p ∈ P, ∀ rho ∈ R p,
      (integralResiduePacket S rho).card ≤ δ ^ 2)
    (hexceptional : (S.filter (fun z ↦ D z = 0)).card ≤ exceptionalBound)
    (hprimeCap : ∀ p ∈ P, p ≤ primeCap)
    (hresidues : ∀ p ∈ P, (R p).card ≤ residueFactor * p) :
    S.card ≤ exceptionalBound +
      P.card * (residueFactor * primeCap) * δ ^ 2 := by
  have h := card_le_exceptional_add_prime_residue_packets
    S D P hP R (fun _ ↦ δ ^ 2) hsize hgood hpacket
  apply h.trans
  apply Nat.add_le_add hexceptional
  calc
    (∑ p ∈ P, (R p).card * δ ^ 2) ≤
        ∑ _p ∈ P, (residueFactor * primeCap) * δ ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact Nat.mul_le_mul_right _
        ((hresidues p hp).trans (Nat.mul_le_mul_left _ (hprimeCap p hp)))
    _ = P.card * (residueFactor * primeCap) * δ ^ 2 := by
      simp [mul_assoc]

end

end TranslatedDepthSeven
