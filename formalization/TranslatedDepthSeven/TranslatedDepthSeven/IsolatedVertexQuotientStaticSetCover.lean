import TranslatedDepthSeven.IsolatedVertexQuotientStaticPacketLabel
import TranslatedDepthSeven.CertificateDeletedReservoirSetCover

/-!
# Static vertex--edge--persistent cover for the quotient branch

This is the set-level conclusion of the isolated-vertex quotient reservoir.
Each regular quotient point carries one fixed integer Jacobian certificate.
For a modulus which avoids that certificate, the component label is formed
from the one integral packet plane already selected by its occupied pair
`(q,rho)`.  The connected deleted-prime reservoir trichotomy then gives a
literal cover by empty labels, nonempty unequal labels on an ambient edge,
and one nonempty ideal which is constant at every surviving modulus.

There is no aggregate cardinal estimate in this file.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

local instance isolatedVertexQuotientStaticSetCoverPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- The finite collection of static quotient component labels which occurs
at a regular point and a modulus surviving its two certificates. -/
def occurringIsolatedVertexQuotientStaticComponentLabels
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1) :
    Finset (Option (Ideal (MvPolynomial (Fin 13) Qbar))) :=
  occurringCertificateDeletedLabels
    (isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations)
    (fun _ ↦ (p.m : ℤ))
    (isolatedVertexQuotientSelectedCertificateValue
      U p sourceEquations CF hx₀ lowerEquations)
    (isolatedVertexQuotientStaticComponentLabel
      U p x₀ sourceEquations CF lowerEquations hquotient
      hqpos hqsf hqlower)

/-- The exact connected vertex--nonempty-edge--persistent cover of the
regular quotient set.  The edge term retains only actual nonempty component
labels. -/
theorem isolatedVertexRegularQuotientPointFinset_subset_staticVertex_edge_persistent
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      (E₂.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k) ∧
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k
        (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected) :
    isolatedVertexRegularQuotientPointFinset
        U p x₀ sourceEquations CF lowerEquations ⊆
      ((Finset.univ : Finset (ReservoirModulus Ppool k)).biUnion fun q ↦
        (isolatedVertexRegularQuotientPointFinset
          U p x₀ sourceEquations CF lowerEquations).filter fun w ↦
          survivesTwoCertificates q (p.m : ℤ)
              (isolatedVertexQuotientSelectedCertificateValue
                U p sourceEquations CF hx₀ lowerEquations w) ∧
            isolatedVertexQuotientStaticComponentLabel
              U p x₀ sourceEquations CF lowerEquations hquotient
              hqpos hqsf hqlower w q = none) ∪
      (((Finset.univ : Finset (ReservoirModulus Ppool k)).biUnion fun q ↦
        (Finset.univ : Finset (ReservoirModulus Ppool k)).biUnion fun r ↦
          (isolatedVertexRegularQuotientPointFinset
            U p x₀ sourceEquations CF lowerEquations).filter fun w ↦
            survivesTwoCertificates q (p.m : ℤ)
                (isolatedVertexQuotientSelectedCertificateValue
                  U p sourceEquations CF hx₀ lowerEquations w) ∧
            survivesTwoCertificates r (p.m : ℤ)
                (isolatedVertexQuotientSelectedCertificateValue
                  U p sourceEquations CF hx₀ lowerEquations w) ∧
            (modulusReservoirGraph Ppool k hP).Adj q r ∧
            isolatedVertexQuotientStaticComponentLabel
                U p x₀ sourceEquations CF lowerEquations hquotient
                hqpos hqsf hqlower w q ≠
              isolatedVertexQuotientStaticComponentLabel
                U p x₀ sourceEquations CF lowerEquations hquotient
                hqpos hqsf hqlower w r ∧
            isolatedVertexQuotientStaticComponentLabel
                U p x₀ sourceEquations CF lowerEquations hquotient
                hqpos hqsf hqlower w q ≠ none ∧
            isolatedVertexQuotientStaticComponentLabel
                U p x₀ sourceEquations CF lowerEquations hquotient
                hqpos hqsf hqlower w r ≠ none) ∪
        (occurringIsolatedVertexQuotientStaticComponentLabels
          U p sourceEquations CF hx₀ lowerEquations hquotient
          Ppool k hqpos hqsf hqlower).biUnion fun o ↦
          (isolatedVertexRegularQuotientPointFinset
            U p x₀ sourceEquations CF lowerEquations).filter fun w ↦
            o ≠ none ∧ ∀ q : ReservoirModulus Ppool k,
              survivesTwoCertificates q (p.m : ℤ)
                  (isolatedVertexQuotientSelectedCertificateValue
                    U p sourceEquations CF hx₀ lowerEquations w) →
              isolatedVertexQuotientStaticComponentLabel
                U p x₀ sourceEquations CF lowerEquations hquotient
                hqpos hqsf hqlower w q = o) := by
  let X := isolatedVertexRegularQuotientPointFinset
    U p x₀ sourceEquations CF lowerEquations
  let D₁ : IntVector 12 → ℤ := fun _ ↦ (p.m : ℤ)
  let D₂ : IntVector 12 → ℤ :=
    isolatedVertexQuotientSelectedCertificateValue
      U p sourceEquations CF hx₀ lowerEquations
  let label : IntVector 12 → ReservoirModulus Ppool k →
      Option (Ideal (MvPolynomial (Fin 13) Qbar)) :=
    isolatedVertexQuotientStaticComponentLabel
      U p x₀ sourceEquations CF lowerEquations hquotient
      hqpos hqsf hqlower
  have hmNe : (p.m : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt p.one_le_m)
  have hmLeH : (p.m : ℝ) ≤ p.H := by
    unfold Parameters.H
    nlinarith [p.hB, p.hL]
  have hHpow : p.H ≤
      p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations := by
    calc
      p.H = p.H ^ (1 : ℕ) := by simp
      _ ≤ p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations :=
        pow_le_pow_right₀ p.one_le_strictHeight
          (one_le_isolatedVertexQuotientCertificateExponent
            U lowerEquations)
  have hmSize : (((p.m : ℤ).natAbs : ℕ) : ℝ) ≤
      p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations := by
    norm_num only [Int.natAbs_natCast, Nat.cast_id]
    exact hmLeH.trans hHpow
  have hconnected : ∀ w ∈ X,
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo Ppool (D₁ w) (D₂ w)) k
        (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected := by
    intro w hw
    exact (hsurvival (D₁ w) (D₂ w) hmNe
      (isolatedVertexQuotientSelectedCertificateValue_ne_zero
        U p sourceEquations CF hx₀ lowerEquations hw)
      hmSize
      (isolatedVertexQuotientSelectedCertificateValue_height
        U p sourceEquations CF hx₀ lowerEquations hw)).2
  have hcover := subset_union_certificateDeleted_reservoir_nonemptyEdges
    hP X D₁ D₂ label hconnected
  simpa only [X, D₁, D₂, label,
    occurringIsolatedVertexQuotientStaticComponentLabels] using hcover

/-- Two unequal nonempty static labels at a regular quotient point are
literal distinct nonradial node components through that point.  Consequently
the point lies on the ideal-theoretic intersection cut out by their supremum.

This is the geometric interpretation of the middle (edge) term in
`isolatedVertexRegularQuotientPointFinset_subset_staticVertex_edge_persistent`;
it introduces no point-counting hypothesis. -/
theorem exists_distinct_retainedNonradialQuotientNodeComponents_and_mem_sup_of_static_edge
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations)
    {q r : ReservoirModulus Ppool k}
    (hqsurvives : survivesTwoCertificates q (p.m : ℤ)
      (isolatedVertexQuotientSelectedCertificateValue
        U p sourceEquations CF hx₀ lowerEquations w))
    (hrsurvives : survivesTwoCertificates r (p.m : ℤ)
      (isolatedVertexQuotientSelectedCertificateValue
        U p sourceEquations CF hx₀ lowerEquations w))
    (hne : isolatedVertexQuotientStaticComponentLabel
        U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower w q ≠
      isolatedVertexQuotientStaticComponentLabel
        U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower w r)
    (hqnonempty : isolatedVertexQuotientStaticComponentLabel
        U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower w q ≠ none)
    (hrnonempty : isolatedVertexQuotientStaticComponentLabel
        U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower w r ≠ none) :
    ∃ Qq Qr : Ideal (MvPolynomial (Fin 13) Qbar),
      Qq ≠ Qr ∧
      isolatedVertexQuotientStaticComponentLabel
          U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower w q = some Qq ∧
      isolatedVertexQuotientStaticComponentLabel
          U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower w r = some Qr ∧
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus (Qq ⊔ Qr) ∧
      IsRetainedNonradialQuotientNodeComponent
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (p.m : ℚ)) Qq ∧
      IsRetainedNonradialQuotientNodeComponent
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (p.m : ℚ)) Qr := by
  classical
  obtain ⟨Qq, hQq⟩ := Option.ne_none_iff_exists'.1 hqnonempty
  obtain ⟨Qr, hQr⟩ := Option.ne_none_iff_exists'.1 hrnonempty
  have hQne : Qq ≠ Qr := by
    intro hEq
    apply hne
    rw [hQq, hQr, hEq]
  have hspecq := isolatedVertexQuotientStaticComponentLabel_eq_some_spec
    U p sourceEquations CF hx₀ lowerEquations hquotient
      hqpos hqsf hqlower hw q hqsurvives hQq
  have hspecr := isolatedVertexQuotientStaticComponentLabel_eq_some_spec
    U p sourceEquations CF hx₀ lowerEquations hquotient
      hqpos hqsf hqlower hw r hrsurvives hQr
  dsimp only at hspecq hspecr
  have hqle : Qq ≤ RingHom.ker
      (MvPolynomial.eval
        (geometricQuotientRationalHomogeneousAffinePoint w)) := by
    intro f hf
    exact RingHom.mem_ker.mpr (hspecq.2.1 f hf)
  have hrle : Qr ≤ RingHom.ker
      (MvPolynomial.eval
        (geometricQuotientRationalHomogeneousAffinePoint w)) := by
    intro f hf
    exact RingHom.mem_ker.mpr (hspecr.2.1 f hf)
  have hsup : geometricQuotientRationalHomogeneousAffinePoint w ∈
      affineIdealZeroLocus (Qq ⊔ Qr) := by
    intro f hf
    exact RingHom.mem_ker.mp ((sup_le hqle hrle) hf)
  exact ⟨Qq, Qr, hQne, hQq, hQr, hsup,
    hspecq.2.2.1, hspecr.2.2.1⟩

end

end TranslatedDepthSeven
