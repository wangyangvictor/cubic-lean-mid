import TranslatedDepthSeven.IsolatedVertexStrictInputBridge
import TranslatedDepthSeven.ManuscriptReservoirTarget
import TranslatedDepthSeven.TangentPacketSpan
import TranslatedDepthSeven.FiniteResiduePacket

/-!
# Tangent packets on the isolated-vertex quotient

The quotient has twelve affine coordinates and dimension five.  At a smooth
residue point its Jacobian therefore has rank at least seven.  The elementary
tangent-minor argument with `k = 9` puts every occupied residue packet in an
affine subspace of direction dimension at most eight once

`9! * (2R)^9 < q^13`,

where `R` is the radius of the transformed quotient box.  This file proves
that statement directly for the literal quotient point set and verifies the
inequality at the manuscript scale `q \gg T^(9/13)`.  No component
decomposition or point-count estimate is assumed here.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 1000000

open NormalizedTangentPacket

/-- Twice the fixed transformed-box coefficient.  Every difference of two
quotient points has absolute value at most this constant times `T`. -/
def isolatedVertexQuotientDifferenceConstant
    (U : IntegralUnimodularChange 13) : ℕ :=
  12 * integralMatrixL1Norm U.forward

/-- A fixed reservoir constant large enough both for the `9 × 9` tangent
minor and for the divided-box estimate. -/
def isolatedVertexQuotientReservoirConstant
    (U : IntegralUnimodularChange 13) : ℕ :=
  Nat.factorial 9 * isolatedVertexQuotientDifferenceConstant U ^ 9 +
    2 * isolatedVertexQuotientDifferenceConstant U + 2

theorem one_lt_isolatedVertexQuotientReservoirConstant
    (U : IntegralUnimodularChange 13) :
    1 < isolatedVertexQuotientReservoirConstant U := by
  unfold isolatedVertexQuotientReservoirConstant
  omega

theorem twice_differenceConstant_le_reservoirConstant
    (U : IntegralUnimodularChange 13) :
    2 * isolatedVertexQuotientDifferenceConstant U ≤
      isolatedVertexQuotientReservoirConstant U := by
  unfold isolatedVertexQuotientReservoirConstant
  omega

theorem isolatedVertexQuotient_tangentCoefficient_lt_constant_pow
    (U : IntegralUnimodularChange 13) :
    Nat.factorial 9 * isolatedVertexQuotientDifferenceConstant U ^ 9 <
      isolatedVertexQuotientReservoirConstant U ^ 13 := by
  let K := isolatedVertexQuotientDifferenceConstant U
  let C := isolatedVertexQuotientReservoirConstant U
  have hlt : Nat.factorial 9 * K ^ 9 < C := by
    dsimp only [C, K, isolatedVertexQuotientReservoirConstant]
    omega
  have hC : 1 ≤ C :=
    (one_lt_isolatedVertexQuotientReservoirConstant U).le
  calc
    Nat.factorial 9 * K ^ 9 < C := hlt
    _ ≤ C ^ 13 := by
      simpa using Nat.pow_le_pow_right hC (show 1 ≤ 13 by omega)

/-- The transformed quotient radius gives the exact difference bound used
in the determinant estimate. -/
theorem twice_isolatedVertexTransformedNaturalSide_cast_le
    (U : IntegralUnimodularChange 13) (p : Parameters) :
    ((2 * isolatedVertexTransformedNaturalSide U p : ℕ) : NNReal) ≤
      isolatedVertexQuotientDifferenceConstant U *
        p.strictNormalizedSide := by
  have h := isolatedVertexTransformedNaturalSide_cast_le U p
  change (isolatedVertexTransformedNaturalSide U p : ℝ) ≤
    (6 * integralMatrixL1Norm U.forward : ℕ) * p.T at h
  change ((2 * isolatedVertexTransformedNaturalSide U p : ℕ) : ℝ) ≤
    (isolatedVertexQuotientDifferenceConstant U : ℕ) * p.T
  unfold isolatedVertexQuotientDifferenceConstant
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h ⊢
  linarith

/-- Exact tangent-minor inequality at quotient scale. -/
theorem isolatedVertexQuotient_tangent_size_inequality
    (U : IntegralUnimodularChange 13)
    {T : NNReal} {q M : ℕ} (hT : 1 ≤ T)
    (hM : (M : NNReal) ≤
      isolatedVertexQuotientDifferenceConstant U * T)
    (hq : (isolatedVertexQuotientReservoirConstant U : NNReal) *
      quotientQScale T ≤ (q : NNReal)) :
    Nat.factorial 9 * M ^ 9 < q ^ 13 := by
  let K := isolatedVertexQuotientDifferenceConstant U
  let C := isolatedVertexQuotientReservoirConstant U
  have hMpow : (M : NNReal) ^ 9 ≤ ((K : NNReal) * T) ^ 9 := by
    gcongr
  have hTpowpos : 0 < T ^ (9 : ℕ) :=
    pow_pos (lt_of_lt_of_le zero_lt_one hT) _
  have hcoeff : (Nat.factorial 9 * K ^ 9 : NNReal) < C ^ 13 := by
    exact_mod_cast isolatedVertexQuotient_tangentCoefficient_lt_constant_pow U
  have hstrict :
      (Nat.factorial 9 : NNReal) * ((K : NNReal) * T) ^ 9 <
        ((C : NNReal) * quotientQScale T) ^ 13 := by
    have hscaleNat : (quotientQScale T) ^ (13 : ℕ) = T ^ (9 : ℕ) := by
      calc
        (quotientQScale T) ^ (13 : ℕ) =
            (quotientQScale T) ^ (13 : ℝ) :=
          (NNReal.rpow_natCast _ _).symm
        _ = T ^ (9 : ℝ) := quotientQScale_rpow_thirteen T
        _ = T ^ (9 : ℕ) := NNReal.rpow_natCast _ _
    calc
      (Nat.factorial 9 : NNReal) * ((K : NNReal) * T) ^ 9 =
          ((Nat.factorial 9 : NNReal) * (K : NNReal) ^ 9) * T ^ 9 := by
        ring
      _ < (C : NNReal) ^ 13 * T ^ 9 :=
        mul_lt_mul_of_pos_right hcoeff hTpowpos
      _ = ((C : NNReal) * quotientQScale T) ^ 13 := by
        rw [mul_pow, hscaleNat]
  have hqpow : ((C : NNReal) * quotientQScale T) ^ 13 ≤
      (q : NNReal) ^ 13 := by
    apply pow_le_pow_left₀ (by positivity)
    simpa only [C] using hq
  have hcast : (Nat.factorial 9 : NNReal) * (M : NNReal) ^ 9 <
      (q : NNReal) ^ 13 := by
    calc
      (Nat.factorial 9 : NNReal) * (M : NNReal) ^ 9 ≤
          (Nat.factorial 9 : NNReal) * ((K : NNReal) * T) ^ 9 := by
        gcongr
      _ < ((C : NNReal) * quotientQScale T) ^ 13 := hstrict
      _ ≤ (q : NNReal) ^ 13 := hqpow
  exact_mod_cast hcast

/-- The integral manuscript target supplies the preceding real lower bound. -/
theorem isolatedVertexQuotient_tangent_size_inequality_of_target
    (U : IntegralUnimodularChange 13) (p : Parameters) {q : ℕ}
    (hq : manuscriptReservoirTarget
      (isolatedVertexQuotientReservoirConstant U : ℝ)
      p.T (9 / 13) ≤ q) :
    Nat.factorial 9 *
        (2 * isolatedVertexTransformedNaturalSide U p) ^ 9 < q ^ 13 := by
  apply isolatedVertexQuotient_tangent_size_inequality U
    (T := p.strictNormalizedSide)
  · exact p.one_le_strictNormalizedSide
  · exact twice_isolatedVertexTransformedNaturalSide_cast_le U p
  · change (isolatedVertexQuotientReservoirConstant U : ℝ) *
      p.T ^ (9 / 13 : ℝ) ≤ (q : ℝ)
    exact (manuscriptReservoirTarget_cast_lower _ _ _).trans
      (by exact_mod_cast hq)

/-- The same reservoir lower endpoint makes every quotient residue packet,
after division by its modulus, lie in a box of side `O(T^(4/13))`. -/
theorem isolatedVertexQuotient_rescaledSide_le_two_rpow
    (U : IntegralUnimodularChange 13) (p : Parameters) {q : ℕ}
    (hq : manuscriptReservoirTarget
      (isolatedVertexQuotientReservoirConstant U : ℝ)
      p.T (9 / 13) ≤ q) :
    1 + (2 * isolatedVertexTransformedNaturalSide U p : ℝ) / q ≤
      2 * p.T ^ (4 / 13 : ℝ) := by
  let K := isolatedVertexQuotientDifferenceConstant U
  let C := isolatedVertexQuotientReservoirConstant U
  have hK : (K : ℝ) ≤ C := by
    exact_mod_cast (Nat.le_trans (Nat.le_mul_of_pos_left K (by omega))
      (twice_differenceConstant_le_reservoirConstant U))
  have hnum : (2 * isolatedVertexTransformedNaturalSide U p : ℝ) ≤
      K * p.T := by
    exact_mod_cast twice_isolatedVertexTransformedNaturalSide_cast_le U p
  have hqtarget : C * p.T ^ (9 / 13 : ℝ) ≤ (q : ℝ) := by
    simpa only [C] using
      (manuscriptReservoirTarget_cast_lower
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13)).trans (by exact_mod_cast hq)
  have hqpos : (0 : ℝ) < q := by
    have hCpos : (0 : ℝ) < C := by
      exact_mod_cast (one_lt_isolatedVertexQuotientReservoirConstant U).trans'
        Nat.zero_lt_one
    have hpowpos : 0 < p.T ^ (9 / 13 : ℝ) :=
      Real.rpow_pos_of_pos p.T_pos _
    nlinarith
  have hpower :
      p.T ^ (4 / 13 : ℝ) * p.T ^ (9 / 13 : ℝ) = p.T := by
    rw [← Real.rpow_add p.T_pos]
    norm_num
  have hdiv : (2 * isolatedVertexTransformedNaturalSide U p : ℝ) / q ≤
      p.T ^ (4 / 13 : ℝ) := by
    rw [div_le_iff₀ hqpos]
    calc
      (2 * isolatedVertexTransformedNaturalSide U p : ℝ) ≤
          K * p.T := hnum
      _ = p.T ^ (4 / 13 : ℝ) *
          (K * p.T ^ (9 / 13 : ℝ)) := by
        calc
          (K : ℝ) * p.T = K *
              (p.T ^ (4 / 13 : ℝ) * p.T ^ (9 / 13 : ℝ)) := by rw [hpower]
          _ = p.T ^ (4 / 13 : ℝ) *
              (K * p.T ^ (9 / 13 : ℝ)) := by ring
      _ ≤ p.T ^ (4 / 13 : ℝ) *
          (C * p.T ^ (9 / 13 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right hK
            (Real.rpow_nonneg p.T_pos.le _)
        · exact Real.rpow_nonneg p.T_pos.le _
      _ ≤ p.T ^ (4 / 13 : ℝ) * q := by
        exact mul_le_mul_of_nonneg_left hqtarget
          (Real.rpow_nonneg p.T_pos.le _)
  have hone : (1 : ℝ) ≤ p.T ^ (4 / 13 : ℝ) :=
    Real.one_le_rpow p.one_le_T (by norm_num)
  linarith

/-- Coordinate differences in a radius-`R` integral box have radius at most
`2R`. -/
theorem intVectorDifference_natAbs_le_twice
    {N : ℕ} {x y : IntVector N} {R : ℕ}
    (hx : ∀ i, (x i).natAbs ≤ R) (hy : ∀ i, (y i).natAbs ≤ R) :
    ∀ i, (x i - y i).natAbs ≤ 2 * R := by
  intro i
  calc
    (x i - y i).natAbs ≤ (x i).natAbs + (y i).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ R + R := Nat.add_le_add (hx i) (hy i)
    _ = 2 * R := by omega

/-- Literal occupied-packet form for a five-dimensional quotient in twelve
affine variables. -/
theorem exists_quotient_affineSubspace_for_occupied_packet
    (equations : Finset (MvPolynomial (Fin 12) ℤ))
    (q R : ℕ) (Z : Finset (IntVector 12))
    (hqpos : 0 < q) (hqsf : Squarefree q)
    (hlarge : Nat.factorial 9 * (2 * R) ^ 9 < q ^ 13)
    (hzero : ∀ z ∈ Z, IntegralCommonZero equations z)
    (hbox : ∀ z ∈ Z, ∀ j, (z j).natAbs ≤ R)
    (rho : Fin 12 → ZMod q)
    (hrho : rho ∈ occupiedIntegralResidues q Z)
    (hrank : ∀ p, p.Prime → p ∣ q →
      7 ≤ (jacobianMatrix (indexedFinsetFamily equations)
        (integralResiduePacketBase Z rho hrho) p).rank) :
    ∃ A : AffineSubspace ℚ (Fin 12 → ℚ),
      Module.finrank ℚ A.direction ≤ 8 ∧
      ∀ z ∈ integralResiduePacket Z rho,
        (fun j ↦ (z j : ℚ)) ∈ A := by
  let Packet := {z : IntVector 12 // z ∈ integralResiduePacket Z rho}
  let y : Packet → IntVector 12 := fun z ↦ z.1
  let i₀ : Packet :=
    ⟨integralResiduePacketBase Z rho hrho,
      integralResiduePacketBase_mem Z rho hrho⟩
  let quotient : Packet → IntVector 12 :=
    congruenceQuotient y i₀ (fun i ↦
      intVectorCongruent_of_mem_same_integralResiduePacket i.2 i₀.2)
  obtain ⟨A, hdim, hmem⟩ :=
    TangentPacketSpan.exists_affineSubspace_of_tangent_packet
      (k := 9) (d := 5) (q := q) (M := 2 * R)
      (indexedFinsetFamily equations) y i₀ quotient hqpos hqsf (by omega)
      (by
        intro z f
        exact hzero z.1 (mem_integralResiduePacket_iff.mp z.2).1
          _ (indexedFinsetFamily_mem equations f))
      (by
        intro z j
        exact congruenceQuotient_spec y i₀
          (fun i ↦ intVectorCongruent_of_mem_same_integralResiduePacket
            i.2 i₀.2) z j)
      (by
        intro p hp hpq
        simpa [jacobianMatrix] using hrank p hp hpq)
      (by
        intro z j
        exact intVectorDifference_natAbs_le_twice
          (hbox z.1 (mem_integralResiduePacket_iff.mp z.2).1)
          (hbox i₀.1 (mem_integralResiduePacket_iff.mp i₀.2).1) j)
      hlarge
  refine ⟨A, by omega, ?_⟩
  intro z hz
  exact hmem ⟨z, hz⟩

/-- Literal rank-seven condition for a five-dimensional affine quotient in
twelve variables. -/
def IsQuotientJacobianRegularAt
    (equations : Finset (MvPolynomial (Fin 12) ℤ))
    (x : IntVector 12) : Prop :=
  7 ≤ ((integralJacobianMatrix (indexedFinsetFamily equations) x).map
    (Int.castRingHom ℚ)).rank

/-- A smooth quotient point produces an explicit nonzero integral Jacobian
minor with a coefficient-height bound involving only the displayed equation
family and point box. -/
theorem exists_quotient_bounded_nonzero_jacobianMinor
    (equations : Finset (MvPolynomial (Fin 12) ℤ))
    (x : IntVector 12) (Y : ℕ)
    (hregular : IsQuotientJacobianRegularAt equations x)
    (hx : ∀ j, (x j).natAbs ≤ Y) :
    ∃ rows : Fin 7 → Fin equations.card,
      ∃ cols : Fin 7 → Fin 12,
        Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor (indexedFinsetFamily equations)
          x rows cols ≠ 0 ∧
        (integralJacobianMinor (indexedFinsetFamily equations)
          x rows cols).natAbs ≤
          Nat.factorial 7 *
            (equationFamilySupportBound equations *
              equationFamilyDegreeBound equations *
              equationFamilyCoefficientBound equations *
              max 1 Y ^ equationFamilyDegreeBound equations) ^ 7 := by
  classical
  have hmem (i : Fin equations.card) :
      indexedFinsetFamily equations i ∈ equations :=
    (equations.equivFin.symm i).2
  apply exists_bounded_nonzero_integralJacobianMinor_of_polynomial_bounds
    (indexedFinsetFamily equations) x hregular
  · intro i
    exact support_card_le_equationFamilySupportBound (hmem i)
  · intro i mu hmu
    exact coeff_natAbs_le_equationFamilyCoefficientBound (hmem i) hmu
  · intro i
    exact totalDegree_le_equationFamilyDegreeBound (hmem i)
  · exact hx

/-- The certificate is chosen before the modulus.  Coprimality of the
eventual square-free modulus with that one nonzero integer supplies rank
seven at every prime divisor and hence the canonical affine eight-plane. -/
theorem exists_bounded_certificate_for_quotient_occupied_packet_then_plane
    (equations : Finset (MvPolynomial (Fin 12) ℤ))
    (q R : ℕ) (Z : Finset (IntVector 12))
    (hqpos : 0 < q) (hqsf : Squarefree q)
    (hlarge : Nat.factorial 9 * (2 * R) ^ 9 < q ^ 13)
    (hzero : ∀ z ∈ Z, IntegralCommonZero equations z)
    (hbox : ∀ z ∈ Z, ∀ j, (z j).natAbs ≤ R)
    (rho : Fin 12 → ZMod q)
    (hrho : rho ∈ occupiedIntegralResidues q Z)
    (hregular : IsQuotientJacobianRegularAt equations
      (integralResiduePacketBase Z rho hrho)) :
    ∃ rows : Fin 7 → Fin equations.card,
      ∃ cols : Fin 7 → Fin 12,
        Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor (indexedFinsetFamily equations)
          (integralResiduePacketBase Z rho hrho) rows cols ≠ 0 ∧
        (integralJacobianMinor (indexedFinsetFamily equations)
          (integralResiduePacketBase Z rho hrho) rows cols).natAbs ≤
          Nat.factorial 7 *
            (equationFamilySupportBound equations *
              equationFamilyDegreeBound equations *
              equationFamilyCoefficientBound equations *
              max 1 R ^ equationFamilyDegreeBound equations) ^ 7 ∧
        (Nat.Coprime q
          (integralJacobianMinor (indexedFinsetFamily equations)
            (integralResiduePacketBase Z rho hrho) rows cols).natAbs →
          ∃ A : AffineSubspace ℚ (Fin 12 → ℚ),
            Module.finrank ℚ A.direction ≤ 8 ∧
            ∀ z ∈ integralResiduePacket Z rho,
              (fun j ↦ (z j : ℚ)) ∈ A) := by
  obtain ⟨rows, cols, hrows, hcols, hminor, hminorBound⟩ :=
    exists_quotient_bounded_nonzero_jacobianMinor equations
      (integralResiduePacketBase Z rho hrho) R hregular
      (hbox _ (mem_integralResiduePacket_iff.mp
        (integralResiduePacketBase_mem Z rho hrho)).1)
  refine ⟨rows, cols, hrows, hcols, hminor, hminorBound, ?_⟩
  intro hcoprime
  apply exists_quotient_affineSubspace_for_occupied_packet
    equations q R Z hqpos hqsf hlarge hzero hbox rho hrho
  intro l hl hlq
  exact jacobian_rank_ge_for_prime_divisors_of_coprime_minor
    (indexedFinsetFamily equations)
    (integralResiduePacketBase Z rho hrho) rows cols hcoprime l hl hlq

/-- Specialization to the exact quotient set and the manuscript lower
endpoint. -/
theorem exists_isolatedVertexQuotient_affineSubspace_for_occupied_packet
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (quotientEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p) quotientEquations)
    (q : ℕ) (hqpos : 0 < q) (hqsf : Squarefree q)
    (hq : manuscriptReservoirTarget
      (isolatedVertexQuotientReservoirConstant U : ℝ)
      p.T (9 / 13) ≤ q)
    (rho : Fin 12 → ZMod q)
    (hrho : rho ∈ occupiedIntegralResidues q
      (isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF))
    (hrank : ∀ l, l.Prime → l ∣ q →
      7 ≤ (jacobianMatrix (indexedFinsetFamily quotientEquations)
        (integralResiduePacketBase
          (isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF)
          rho hrho) l).rank) :
    ∃ A : AffineSubspace ℚ (Fin 12 → ℚ),
      Module.finrank ℚ A.direction ≤ 8 ∧
      ∀ z ∈ integralResiduePacket
          (isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF) rho,
        (fun j ↦ (z j : ℚ)) ∈ A := by
  apply exists_quotient_affineSubspace_for_occupied_packet quotientEquations
    q (isolatedVertexTransformedNaturalSide U p)
    (isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF)
    hqpos hqsf
    (isolatedVertexQuotient_tangent_size_inequality_of_target U p hq)
  · intro z hz
    exact (mem_integralCommonZeroInBox_iff quotientEquations z).mp
      (hquotient hz) |>.2
  · intro z hz
    exact (mem_integralCommonZeroInBox_iff quotientEquations z).mp
      (hquotient hz) |>.1
  · exact hrank

end

end TranslatedDepthSeven
