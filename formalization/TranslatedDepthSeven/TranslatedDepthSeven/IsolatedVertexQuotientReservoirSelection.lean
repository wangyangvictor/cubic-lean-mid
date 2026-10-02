import TranslatedDepthSeven.IsolatedVertexQuotientCertificateHeight
import TranslatedDepthSeven.ManuscriptModulusReservoir
import TranslatedDepthSeven.CertificateDeletedReservoirPartition
import TranslatedDepthSeven.StaticChartReservoirCover

/-!
# Pointwise deletion in the isolated-vertex quotient reservoir

For a regular integral quotient point, the Jacobian minor is chosen before
the modulus.  Deleting the prime divisors of that minor and of the affine
scale produces a member of the original square-free reservoir.  Congruence
transports the minor from the chosen point to the fixed base of its residue
packet, so the literal quotient tangent theorem puts the whole packet in an
affine subspace of direction dimension at most eight.

No component decomposition or point-count estimate is assumed here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open Filter
open scoped Topology

local instance isolatedVertexQuotientReservoirPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

theorem one_le_isolatedVertexQuotientCertificateExponent
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    1 ≤ isolatedVertexQuotientCertificateExponent U lowerEquations := by
  unfold isolatedVertexQuotientCertificateExponent
  dsimp only
  omega

/-- Exact pointwise output of deleting the scale and the quotient Jacobian
certificate from a fixed reservoir. -/
theorem exists_isolatedVertexQuotient_survivingModulus_and_packetPlane
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (P : Finset ℕ) (k : ℕ) (hP : ∀ l ∈ P, l.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hsquarefree : ∀ q : ReservoirModulus P k, Squarefree q.1)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      (E₂.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P E₁ E₂) k))
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexQuotientPointFinset
      U p x₀ sourceEquations CF)
    (hregular : IsQuotientJacobianRegularAt
      (isolatedVertexQuotientAffineEquationFinset
        U p x₀ lowerEquations) w) :
    ∃ q : ReservoirModulus P k,
      Nat.Coprime q.1 p.m ∧
      ∃ rows : Fin 7 → Fin
          (isolatedVertexQuotientAffineEquationFinset
            U p x₀ lowerEquations).card,
        ∃ cols : Fin 7 → Fin 12,
          Function.Injective rows ∧ Function.Injective cols ∧
          integralJacobianMinor
            (indexedFinsetFamily
              (isolatedVertexQuotientAffineEquationFinset
                U p x₀ lowerEquations)) w rows cols ≠ 0 ∧
          Nat.Coprime q.1
            (integralJacobianMinor
              (indexedFinsetFamily
                (isolatedVertexQuotientAffineEquationFinset
                  U p x₀ lowerEquations)) w rows cols).natAbs ∧
          ∃ A : AffineSubspace ℚ (Fin 12 → ℚ),
            Module.finrank ℚ A.direction ≤ 8 ∧
            ∀ z ∈ integralResiduePacket
                (isolatedVertexQuotientPointFinset
                  U p x₀ sourceEquations CF)
                (integralResidueVector w : Fin 12 → ZMod q.1),
              (fun j ↦ (z j : ℚ)) ∈ A := by
  let equationsQ :=
    isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations
  let E := isolatedVertexQuotientCertificateExponent U lowerEquations
  obtain ⟨rows, cols, hrows, hcols, hminor, hminorSize⟩ :=
    exists_quotientAffineEquation_jacobianCertificate_le_heightPower
      U p sourceEquations CF hx₀ lowerEquations hw hregular
  have hmNe : (p.m : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt p.one_le_m)
  have hminorNe :
      integralJacobianMinor (indexedFinsetFamily equationsQ)
        w rows cols ≠ 0 := by
    simpa only [equationsQ] using hminor
  have hm : (p.m : ℝ) ≤ p.H := by
    unfold Parameters.H
    nlinarith [p.hB, p.hL]
  have hHpow : p.H ≤ p.H ^ E := by
    have hE : 1 ≤ E := by
      simpa only [E] using
        one_le_isolatedVertexQuotientCertificateExponent U lowerEquations
    calc
      p.H = p.H ^ (1 : ℕ) := by simp
      _ ≤ p.H ^ E := by
        exact pow_le_pow_right₀ p.one_le_strictHeight hE
  have hmSize : (((p.m : ℤ).natAbs : ℕ) : ℝ) ≤ p.H ^ E := by
    norm_num only [Int.natAbs_natCast, Nat.cast_id]
    exact hm.trans hHpow
  have hminorSize' :
      ((integralJacobianMinor (indexedFinsetFamily equationsQ)
        w rows cols).natAbs : ℝ) ≤ p.H ^ E := by
    simpa only [equationsQ, E] using hminorSize
  obtain ⟨qAllowed⟩ := hsurvival (p.m : ℤ)
    (integralJacobianMinor (indexedFinsetFamily equationsQ) w rows cols)
    hmNe hminorNe hmSize hminorSize'
  let q : ReservoirModulus P k :=
    certificateAllowedTwoModulusEmbedding hP (p.m : ℤ)
      (integralJacobianMinor (indexedFinsetFamily equationsQ)
        w rows cols) qAllowed
  have hsurvives : survivesTwoCertificates q (p.m : ℤ)
      (integralJacobianMinor (indexedFinsetFamily equationsQ)
        w rows cols) :=
    certificateAllowedTwoModulusEmbedding_survives hP (p.m : ℤ)
      (integralJacobianMinor (indexedFinsetFamily equationsQ)
        w rows cols) qAllowed
  have hcopm : Nat.Coprime q.1 p.m := by
    simpa only [Int.natAbs_natCast] using hsurvives.1
  have hcopminor : Nat.Coprime q.1
      (integralJacobianMinor (indexedFinsetFamily equationsQ)
        w rows cols).natAbs := hsurvives.2
  let Z := isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF
  let rho : Fin 12 → ZMod q.1 := integralResidueVector w
  have hrho : rho ∈ occupiedIntegralResidues q.1 Z := by
    exact Finset.mem_image.mpr ⟨w, by simpa only [Z] using hw, rfl⟩
  have hwPacket : w ∈ integralResiduePacket Z rho :=
    mem_integralResiduePacket_iff.mpr
      ⟨by simpa only [Z] using hw, rfl⟩
  have hbasePacket : integralResiduePacketBase Z rho hrho ∈
      integralResiduePacket Z rho :=
    integralResiduePacketBase_mem Z rho hrho
  have hcongr : IntVectorCongruent q.1 w
      (integralResiduePacketBase Z rho hrho) :=
    intVectorCongruent_of_mem_same_integralResiduePacket
      hwPacket hbasePacket
  have hcopBase : Nat.Coprime q.1
      (integralJacobianMinor (indexedFinsetFamily equationsQ)
        (integralResiduePacketBase Z rho hrho) rows cols).natAbs := by
    have hcopAtW : Nat.Coprime q.1
        (MvPolynomial.eval w
          (integralJacobianMinorPolynomial
            (indexedFinsetFamily equationsQ) rows cols)).natAbs := by
      simpa only [eval_integralJacobianMinorPolynomial] using hcopminor
    have hcopEval := coprime_eval_natAbs_of_coordinate_cast_eq
      (integralJacobianMinorPolynomial
        (indexedFinsetFamily equationsQ) rows cols)
      w (integralResiduePacketBase Z rho hrho) hcongr hcopAtW
    simpa only [eval_integralJacobianMinorPolynomial] using hcopEval
  have hqpos : 0 < q.1 := by
    have hCpos : (0 : ℝ) <
        isolatedVertexQuotientReservoirConstant U := by
      exact_mod_cast (one_lt_isolatedVertexQuotientReservoirConstant U).trans'
        Nat.zero_lt_one
    have htargetPos : (0 : ℝ) <
        (isolatedVertexQuotientReservoirConstant U : ℝ) *
          p.T ^ (9 / 13 : ℝ) :=
      mul_pos hCpos (Real.rpow_pos_of_pos p.T_pos _)
    have htargetLe :
        (isolatedVertexQuotientReservoirConstant U : ℝ) *
            p.T ^ (9 / 13 : ℝ) ≤ q.1 :=
      (manuscriptReservoirTarget_cast_lower
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13)).trans (by exact_mod_cast hlower q)
    exact_mod_cast htargetPos.trans_le htargetLe
  have hrank : ∀ l, l.Prime → l ∣ q.1 →
      7 ≤ (jacobianMatrix (indexedFinsetFamily equationsQ)
        (integralResiduePacketBase Z rho hrho) l).rank :=
    jacobian_rank_ge_for_prime_divisors_of_coprime_minor
      (indexedFinsetFamily equationsQ)
      (integralResiduePacketBase Z rho hrho) rows cols hcopBase
  obtain ⟨A, hAdim, hAcontains⟩ :=
    exists_isolatedVertexQuotient_affineSubspace_for_occupied_packet
      U p x₀ sourceEquations CF equationsQ
      (by simpa only [Z, equationsQ] using hquotient)
      q.1 hqpos (hsquarefree q) (hlower q) rho hrho hrank
  refine ⟨q, hcopm, rows, cols, hrows, hcols, ?_, ?_, A, hAdim, ?_⟩
  · simpa only [equationsQ] using hminor
  · simpa only [equationsQ] using hcopminor
  · simpa only [Z, rho] using hAcontains

/-- The canonical `T^(9/13)` reservoir simultaneously supplies the exact
vertex/edge occurrence count, the modulus and lcm ranges, and a surviving
affine eight-plane for every regular point of the literal quotient set. -/
theorem eventually_exists_isolatedVertexQuotientReservoir_and_packetPlanes
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ (p : Parameters), p.H = H →
      ∃ (P : Finset ℕ) (k : ℕ) (hP : ∀ l ∈ P, l.Prime),
        P = manuscriptPrimePoolAt
          (isolatedVertexQuotientCertificateExponent U lowerEquations : ℝ)
          (9 / 13) H ∧
        k = manuscriptCrossingAt
          (isolatedVertexQuotientCertificateExponent U lowerEquations : ℝ)
          (9 / 13)
          (isolatedVertexQuotientReservoirConstant U : ℝ) H p.T ∧
        k ≤ P.card ∧
        ((((modulusReservoir P k).card +
            (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
          2 * H ^ ε) ∧
        (∀ q : ReservoirModulus P k,
          Squarefree q.1 ∧
          (isolatedVertexQuotientReservoirConstant U : ℝ) *
              p.T ^ (9 / 13 : ℝ) ≤ q.1 ∧
          (q.1 : ℝ) ≤
            (4 * manuscriptPrimeIntervalCoefficient
                (isolatedVertexQuotientCertificateExponent
                  U lowerEquations : ℝ) (9 / 13) * (ε / 3)⁻¹) *
              (isolatedVertexQuotientReservoirConstant U : ℝ) *
              p.T ^ (9 / 13 : ℝ) * H ^ ε) ∧
        (∀ q r : ReservoirModulus P k,
          (modulusReservoirGraph P k hP).Adj q r →
            (isolatedVertexQuotientReservoirConstant U : ℝ) *
                p.T ^ (9 / 13 : ℝ) ≤
                  (Nat.lcm q.1 r.1 : ℝ) ∧
            (Nat.lcm q.1 r.1 : ℝ) ≤
              (16 * (manuscriptPrimeIntervalCoefficient
                  (isolatedVertexQuotientCertificateExponent
                    U lowerEquations : ℝ) (9 / 13)) ^ 2 *
                    ((ε / 3)⁻¹) ^ 2) *
                (isolatedVertexQuotientReservoirConstant U : ℝ) *
                p.T ^ (9 / 13 : ℝ) * H ^ ε) ∧
        ∀ (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
          (x₀ : IntVector 13),
          x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF →
          isolatedVertexQuotientPointFinset U p x₀
              sourceEquations CF ⊆ integralCommonZeroInBox
                (M := isolatedVertexTransformedNaturalSide U p)
                (isolatedVertexQuotientAffineEquationFinset
                  U p x₀ lowerEquations) →
          ∀ w ∈ isolatedVertexQuotientPointFinset
              U p x₀ sourceEquations CF,
            IsQuotientJacobianRegularAt
                (isolatedVertexQuotientAffineEquationFinset
                  U p x₀ lowerEquations) w →
            ∃ q : ReservoirModulus P k,
              Nat.Coprime q.1 p.m ∧
              ∃ A : AffineSubspace ℚ (Fin 12 → ℚ),
                Module.finrank ℚ A.direction ≤ 8 ∧
                ∀ z ∈ integralResiduePacket
                    (isolatedVertexQuotientPointFinset
                      U p x₀ sourceEquations CF)
                    (integralResidueVector w : Fin 12 → ZMod q.1),
                  (fun j ↦ (z j : ℚ)) ∈ A := by
  let E := isolatedVertexQuotientCertificateExponent U lowerEquations
  let C := isolatedVertexQuotientReservoirConstant U
  have hEnonneg : (0 : ℝ) ≤ E := by positivity
  have ha : (0 : ℝ) < 9 / 13 := by norm_num
  have haOne : (9 / 13 : ℝ) < 1 := by norm_num
  have hC : (1 : ℝ) < C := by
    exact_mod_cast one_lt_isolatedVertexQuotientReservoirConstant U
  filter_upwards [eventually_exists_manuscriptModulusReservoir
    (A := (E : ℝ)) (a := (9 / 13 : ℝ)) (Cres := (C : ℝ))
      hEnonneg ha haOne hC hε] with H hreservoir
  intro p hpH
  have hTH : p.T ≤ H := by
    rw [← hpH]
    exact p.T_le_H
  obtain ⟨P, k, hP, hPcanonical, hkcanonical, _hPcard,
      _hPinterval, hkP, hmoduli, _hconnected, hfamily, hlcm,
      _hcertOne, hcertTwo⟩ :=
    hreservoir p.T p.one_le_T hTH
  have hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget (C : ℝ) p.T (9 / 13) ≤ q.1 := by
    intro q
    apply Nat.ceil_le.mpr
    exact (hmoduli q).2.1
  refine ⟨P, k, hP, ?_, ?_, hkP, hfamily, hmoduli, hlcm, ?_⟩
  · simpa only [E] using hPcanonical
  · simpa only [E, C] using hkcanonical
  intro sourceEquations CF x₀ hx₀ hquotient w hw hregular
  have hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤ p.H ^ E →
      (E₂.natAbs : ℝ) ≤ p.H ^ E →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P E₁ E₂) k) := by
    intro E₁ E₂ hE₁ hE₂ hE₁size hE₂size
    have hE₁size' : (E₁.natAbs : ℝ) ≤ H ^ (E : ℝ) := by
      simpa only [← hpH, Real.rpow_natCast] using hE₁size
    have hE₂size' : (E₂.natAbs : ℝ) ≤ H ^ (E : ℝ) := by
      simpa only [← hpH, Real.rpow_natCast] using hE₂size
    exact (hcertTwo E₁ E₂ hE₁ hE₂ hE₁size' hE₂size').2.1
  obtain ⟨q, hqm, rows, cols, hrows, hcols, hminor,
      hqminor, A, hAdim, hAcontains⟩ :=
    exists_isolatedVertexQuotient_survivingModulus_and_packetPlane
      U p sourceEquations CF hx₀ lowerEquations hquotient P k hP
      (by simpa only [C] using hlower)
      (fun q ↦ (hmoduli q).1) (by simpa only [E] using hsurvival)
      hw hregular
  exact ⟨q, hqm, A, hAdim, hAcontains⟩

end

end TranslatedDepthSeven
