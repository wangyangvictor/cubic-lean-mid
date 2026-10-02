import CubicTenVariables.FixedLeadingSurfaceLogarithmicPacketHeightAuxiliary
import TranslatedDepthSeven.HypersurfaceSmoothPrimePacket
import TranslatedDepthSeven.FixedConeOccupiedResidueCRT
import TranslatedDepthSeven.PrimeSubsetPrefixReservoirBridge
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Logarithmic auxiliaries on surviving residue fibres

This is the logarithmic-degree sibling of
`FixedLeadingSurfaceSurvivorAuxiliaryChoice`.  The fixed constant `L`, the
coordinates, and the height threshold precede every varying equation and
point set.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace CubicTenVariables.FixedLeadingSurfaceLogarithmicSurvivorAuxiliaryChoice

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateChoice FixedLeadingSurfaceCoordinateTransport

theorem exists_uniform_logarithmic_prefix_auxiliaries
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {d e : ℕ} (hd : 2 ≤ d)
    (k₀ : MvPolynomial (Fin 3) ℤ) (hk₀ : k₀.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k₀))
    (K : ℝ) (hK : 1 < K) (A : ℕ)
    (alpha : ℝ) (halpha : Real.sqrt K / Real.sqrt (d : ℝ) < alpha) :
    ∃ (a b : ℤ) (L : ℝ) (H₀ : ℕ),
      (coordinateMatrix a b).det = 1 ∧ 1 ≤ L ∧ 2 ≤ H₀ ∧
      ∀ (P : Finset ℕ) (depth H B m : ℕ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, ¬ p ∣ m) →
      H₀ ≤ H → 1 ≤ B → m ≠ 0 →
      (∀ v : PrimeSubsetPrefix.Vertex P depth,
        m * PrimeSubsetPrefix.modulus v ≤ H ^ A) →
      ∃ blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ,
        (∀ v, 0 < blockDegree v ∧
          (blockDegree v : ℝ) ≤ 2 * L * Real.log (H : ℝ) *
            (1 + (B : ℝ) ^ alpha /
              (PrimeSubsetPrefix.modulus v : ℝ))) ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
        g.totalDegree ≤ d →
        map (Int.castRingHom ℚ) (homogeneousComponent d g) =
          C c * map (Int.castRingHom ℚ) k₀ →
        mvPolynomialCoefficientNatAbsMax g ≤ H ^ e →
        let F := projectiveEquiv a b (homogenize d g)
        ∀ (u : Fin 3 → ℤ) (X : Finset (Fin 3 → ℤ))
          (allowed : (Fin 3 → ℤ) → Finset ℕ),
        (∀ z ∈ X, ∀ i, (progressionHomogeneousPoint u m z i).natAbs ≤ H) →
        (∀ z ∈ X, ∀ i, (z i).natAbs ≤ B) →
        (∀ z ∈ X, eval (progressionHomogeneousPoint u m z) F = 0) →
        (∀ z ∈ X, ∃ i, eval (fun j => u j + (m : ℤ) * z j)
          (pderiv i (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
        (∀ z ∈ X, ∀ p ∈ allowed z, ∃ i,
          (eval (fun j => u j + (m : ℤ) * z j)
            (pderiv i (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
        ∃ auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) → MvPolynomial (Fin 4) ℚ,
          ∀ z ∈ X, ∀ v ∈ PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
            (auxiliary v (integralResidueVector z)).IsHomogeneous
              (d - 1 + blockDegree v) ∧
            auxiliary v (integralResidueVector z) ∉
              Ideal.span {map (Int.castRingHom ℚ) F} ∧
            eval (fun i => (progressionHomogeneousPoint u m z i : ℚ))
              (auxiliary v (integralResidueVector z)) = 0 := by
  classical
  obtain ⟨a, b, L, H₀, hdet, hL, hH₀, hfamily⟩ :=
    CubicTenVariables.FixedLeadingSurfaceLogarithmicPacketHeightAuxiliary.exists_uniform_logarithmic_auxiliaryFamily_of_packet_height
        (e := e) integralityOpen curveWeil hd k₀ hk₀ hirr K hK A alpha halpha
  refine ⟨a, b, L, H₀, hdet, hL, hH₀, ?_⟩
  intro P depth H B m hP hPm hH hB hm hmoduli
  have hvPrime (v : PrimeSubsetPrefix.Vertex P depth) : ∀ p ∈ v.1, p.Prime :=
    fun p hp => hP p ((PrimeSubsetPrefix.mem_vertices.mp v.2).1 hp)
  have hqpos (v : PrimeSubsetPrefix.Vertex P depth) :
      0 < PrimeSubsetPrefix.modulus v :=
    Nat.pos_of_ne_zero (primeProduct_ne_zero (hvPrime v))
  have hqheight (v : PrimeSubsetPrefix.Vertex P depth) :
      PrimeSubsetPrefix.modulus v ≤ H ^ A := by
    have hmul : PrimeSubsetPrefix.modulus v ≤
        m * PrimeSubsetPrefix.modulus v := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right (PrimeSubsetPrefix.modulus v)
          (Nat.one_le_iff_ne_zero.mpr hm)
    exact hmul.trans (hmoduli v)
  have hchoice := fun v : PrimeSubsetPrefix.Vertex P depth =>
    hfamily H B (PrimeSubsetPrefix.modulus v) hH hB (hqpos v) (hqheight v)
  choose blockDegree hblockPos hblockBound hpacket using hchoice
  refine ⟨blockDegree, fun v => ⟨hblockPos v, hblockBound v⟩, ?_⟩
  intro g c hc hdegree htop hheight
  dsimp only
  intro u X allowed hsource hbox hzero hgrad hsmooth
  let F := projectiveEquiv a b (homogenize d g)
  let eligible (v : PrimeSubsetPrefix.Vertex P depth) :=
    X.filter fun z => v ∈ PrimeSubsetPrefix.survivingVertices P (allowed z) depth
  have heX (v : PrimeSubsetPrefix.Vertex P depth) : eligible v ⊆ X :=
    Finset.filter_subset _ _
  have hvertex : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      ∃ aux : (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
          MvPolynomial (Fin 4) ℚ,
        ∀ z ∈ eligible v,
          (aux (integralResidueVector z)).IsHomogeneous
              (d - 1 + blockDegree v) ∧
          aux (integralResidueVector z) ∉
              Ideal.span {map (Int.castRingHom ℚ) F} ∧
          eval (fun i => (progressionHomogeneousPoint u m z i : ℚ))
            (aux (integralResidueVector z)) = 0 := by
    intro v
    have hvP : v.1 ⊆ P := (PrimeSubsetPrefix.mem_vertices.mp v.2).1
    have hsq : Squarefree (PrimeSubsetPrefix.modulus v) :=
      primeProduct_squarefree (hvPrime v)
    have hqm : Nat.Coprime (PrimeSubsetPrefix.modulus v) m := by
      rw [PrimeSubsetPrefix.modulus, primeProduct, Nat.coprime_prod_left_iff]
      intro p hp
      exact (hvPrime v p hp).coprime_iff_not_dvd.mpr (hPm p (hvP hp))
    have hcell : ∀ rho :
        ↑(occupiedIntegralResidues (PrimeSubsetPrefix.modulus v) (eligible v)),
        ∃ Q : MvPolynomial (Fin 4) ℚ,
          Q.IsHomogeneous (d - 1 + blockDegree v) ∧
          Q ∉ Ideal.span {map (Int.castRingHom ℚ) F} ∧
          ∀ z ∈ eligible v, integralResidueVector z = rho.1 →
            eval (fun i => (progressionHomogeneousPoint u m z i : ℚ)) Q = 0 := by
      intro rho
      obtain ⟨z, hz, hzr⟩ := mem_occupiedIntegralResidues_iff.mp rho.2
      let Y := (eligible v).filter fun y => integralResidueVector y = rho.1
      let f := Fintype.equivFin ↑Y
      let y : Fin (Fintype.card ↑Y) → Fin 3 → ℤ := fun j => (f.symm j).1
      have hyE : ∀ j, y j ∈ eligible v := fun j =>
        (Finset.mem_filter.mp (f.symm j).2).1
      have hyq : ∀ j i, (PrimeSubsetPrefix.modulus v : ℤ) ∣ y j i - z i := by
        intro j i
        apply (ZMod.intCast_eq_intCast_iff_dvd_sub (z i) (y j i)
          (PrimeSubsetPrefix.modulus v)).mp
        have hyr := (Finset.mem_filter.mp (f.symm j).2).2
        exact (congrFun hzr i).trans (congrFun hyr i).symm
      have hsmoothz : ∀ p, p.Prime → p ∣ PrimeSubsetPrefix.modulus v → ∃ i,
          (eval (fun j => u j + (m : ℤ) * z j)
            (pderiv i (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0 := by
        intro p hp hpq
        have hpv : p ∈ v.1 := by
          rw [← primeFactors_primeProduct (hvPrime v)]
          exact Nat.mem_primeFactors.mpr
            ⟨hp, hpq, primeProduct_ne_zero (hvPrime v)⟩
        exact hsmooth z (heX v hz) p
          ((PrimeSubsetPrefix.mem_survivingVertices_iff v).mp
            (Finset.mem_filter.mp hz).2 hpv)
      obtain ⟨Q, hhom, hnot, hvanish⟩ :=
        hpacket v g c hc hdegree htop hheight m (Fintype.card ↑Y) u y
          (hmoduli v) hm hsq
          (fun j => hsource _ (heX v (hyE j)))
          (fun j => hbox _ (heX v (hyE j)))
          (fun j => hzero _ (heX v (hyE j)))
          (fun j => hgrad _ (heX v (hyE j)))
          (hypersurfaceProgression_packet_inputs_of_usable_modulus
            F u z y m (PrimeSubsetPrefix.modulus v) hqm hyq hsmoothz)
      refine ⟨Q, hhom, hnot, ?_⟩
      intro w hw hwr
      have hwY : w ∈ Y := Finset.mem_filter.mpr ⟨hw, hwr⟩
      simpa only [y, Equiv.symm_apply_apply] using hvanish (f ⟨w, hwY⟩)
    choose Q hQhom hQnot hQvanish using hcell
    let aux : (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ :=
      fun rho => if hrho : rho ∈
          occupiedIntegralResidues (PrimeSubsetPrefix.modulus v) (eligible v)
        then Q ⟨rho, hrho⟩ else 0
    refine ⟨aux, ?_⟩
    intro z hz
    have hrho : integralResidueVector z ∈
        occupiedIntegralResidues (PrimeSubsetPrefix.modulus v) (eligible v) :=
      mem_occupiedIntegralResidues_iff.mpr ⟨z, hz, rfl⟩
    simp only [aux, dif_pos hrho]
    exact ⟨hQhom ⟨_, hrho⟩, hQnot ⟨_, hrho⟩,
      hQvanish ⟨_, hrho⟩ z hz rfl⟩
  choose auxiliary hauxiliary using hvertex
  refine ⟨auxiliary, ?_⟩
  intro z hz v hv
  exact hauxiliary v z (Finset.mem_filter.mpr ⟨hz, hv⟩)

end CubicTenVariables.FixedLeadingSurfaceLogarithmicSurvivorAuxiliaryChoice
