import TranslatedDepthSeven.FixedSurfaceQuantitativePacketPrimeRangeAuxiliary
import TranslatedDepthSeven.HypersurfaceSmoothPrimePacket
import TranslatedDepthSeven.FixedConeOccupiedResidueCRT

/-!
# Residue-dependent quantitative surface auxiliaries

The quantitative packet theorem is applied simultaneously to every occupied
residue class.  One degree is selected before the packets, and classical
choice then gives an actual auxiliary polynomial as a function of the
residue.  This is the form needed by the rooted component graph and by the
changed-edge record count.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 250000

/-- All occupied residue packets receive proper auxiliaries of one common
degree.  The degree is chosen before the residue class and satisfies the
sharp packet-modulus dependence. -/
theorem exists_fixedSurface_quantitative_residueAuxiliaryChoice
    {d : ℕ} (hd : 0 < d)
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℚ))
    (hX : MvPolynomial.X 0 ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (F : MvPolynomial (Fin 4) ℤ)
    (K : ℝ) (hK : 1 ≤ K) (Aex : ℕ)
    (η a : ℝ) (hη : 0 < η)
    (ha : Real.sqrt K / Real.sqrt (d : ℝ) < a) :
    ∃ b D A H₀ : ℕ, ∃ C : ℝ,
      1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧ 0 ≤ C ∧
      ∀ (H B q m Dex : ℕ) (u : Fin 3 → ℤ)
        (X : Finset (Fin 3 → ℤ)),
      H₀ ≤ H → 1 ≤ B →
      0 < Dex → Dex ≤ H ^ Aex → m * q ∣ Dex →
      m ≠ 0 → 0 < q → Squarefree q → Nat.Coprime q m →
      (∀ p, p.Prime → ¬ p ∣ Dex →
        (Nat.card (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
            K * (p : ℝ) ^ 2) →
      (∀ z ∈ X, ∀ i,
        (progressionHomogeneousPoint u m z i).natAbs ≤ H) →
      (∀ z ∈ X, ∀ i, (z i).natAbs ≤ B) →
      (∀ z ∈ X,
        MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0) →
      (∀ z ∈ X, ∃ v, MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
        (MvPolynomial.pderiv v
          (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ z ∈ X, ∀ p, p.Prime → p ∣ q → ∃ v,
        (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
          (MvPolynomial.pderiv v
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      ∃ k : ℕ, 0 < k ∧
        (k : ℝ) ≤ 2 * (H : ℝ) ^ η *
          (1 + (B : ℝ) ^ a / (q : ℝ)) ∧
        ∃ auxiliary : (Fin 3 → ZMod q) → MvPolynomial (Fin 4) ℚ,
          (∀ ρ ∈ occupiedIntegralResidues q X,
            (auxiliary ρ).IsHomogeneous (b + k) ∧ auxiliary ρ ∉ I) ∧
          ∀ z ∈ X, MvPolynomial.eval
            (fun i => (progressionHomogeneousPoint u m z i : ℚ))
              (auxiliary (integralResidueVector z)) = 0 := by
  classical
  obtain ⟨b, D, A, H₀, C, hD, hA, hH₀, hC, hfamily⟩ :=
    exists_fixedSurface_quantitative_auxiliaryFamily_of_packetPrimeRange
      hd I hprime hhom hX hdegree F K hK Aex η a hη ha
  refine ⟨b, D, A, H₀, C, hD, hA, hH₀, hC, ?_⟩
  intro H B q m Dex u X hH hB hDex hDexHeight hmqdvd hm hq hsq hqm
    hpoints hsource hdisplacement hzero hgrad hsmooth
  have hqheightNat : q ≤ H ^ Aex := by
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hmqle : m * q ≤ Dex := Nat.le_of_dvd hDex hmqdvd
    have hqle : q ≤ m * q := by
      nlinarith [Nat.one_le_iff_ne_zero.mpr hm]
    exact hqle.trans (hmqle.trans hDexHeight)
  have hqheight : (q : ℝ) ≤ (H : ℝ) ^ (Aex : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hqheightNat
  obtain ⟨k, hk, hkbound, haux⟩ :=
    hfamily H B q hH hB (Nat.one_le_iff_ne_zero.mpr hq.ne') hqheight
  have hcell : ∀ c : ↥(occupiedIntegralResidues q X),
      ∃ Q : MvPolynomial (Fin 4) ℚ,
        Q.IsHomogeneous (b + k) ∧ Q ∉ I ∧
        ∀ z ∈ X, integralResidueVector z = c.1 →
          MvPolynomial.eval
            (fun i => (progressionHomogeneousPoint u m z i : ℚ)) Q = 0 := by
    intro c
    obtain ⟨z, hz, hzc⟩ := mem_occupiedIntegralResidues_iff.mp c.2
    let Y := X.filter (fun y => integralResidueVector y = c.1)
    let f := Fintype.equivFin ↥Y
    let y : Fin (Fintype.card ↥Y) → Fin 3 → ℤ := fun j => (f.symm j).1
    have hyX : ∀ j, y j ∈ X := fun j => (Finset.mem_filter.mp (f.symm j).2).1
    have hyq : ∀ j i, (q : ℤ) ∣ y j i - z i := by
      intro j i
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub (z i) (y j i) q).mp
      have hyc := (Finset.mem_filter.mp (f.symm j).2).2
      exact (congrFun hzc i).trans (congrFun hyc i).symm
    obtain ⟨Q, hQhom, hQI, hQzero⟩ :=
      haux m (Fintype.card ↥Y) Dex u y hDex hDexHeight hmqdvd hm hq hsq
        hpoints (fun j => hsource _ (hyX j))
        (fun j => hdisplacement _ (hyX j))
        (fun j => hzero _ (hyX j)) (fun j => hgrad _ (hyX j))
        (hypersurfaceProgression_packet_inputs_of_usable_modulus
          F u z y m q hqm hyq (hsmooth z hz))
    refine ⟨Q, hQhom, hQI, ?_⟩
    intro w hw hwc
    have hwY : w ∈ Y := Finset.mem_filter.mpr ⟨hw, hwc⟩
    simpa only [y, Equiv.symm_apply_apply] using hQzero (f ⟨w, hwY⟩)
  choose Q hQhom hQI hQzero using hcell
  let auxiliary : (Fin 3 → ZMod q) → MvPolynomial (Fin 4) ℚ := fun ρ =>
    if hρ : ρ ∈ occupiedIntegralResidues q X then Q ⟨ρ, hρ⟩ else 0
  refine ⟨k, hk, hkbound, auxiliary, ?_, ?_⟩
  · intro ρ hρ
    simp only [auxiliary, dif_pos hρ]
    exact ⟨hQhom ⟨ρ, hρ⟩, hQI ⟨ρ, hρ⟩⟩
  · intro z hz
    have hρ : integralResidueVector z ∈ occupiedIntegralResidues q X :=
      mem_occupiedIntegralResidues_iff.mpr ⟨z, hz, rfl⟩
    simp only [auxiliary, dif_pos hρ]
    exact hQzero ⟨integralResidueVector z, hρ⟩ z hz rfl

end
end TranslatedDepthSeven
