import TranslatedDepthSeven.CoefficientExtensionHomogeneousIdeal
import TranslatedDepthSeven.RealCoefficientExtension
import TranslatedDepthSeven.RealProjectiveHilbertExtension
import TranslatedDepthSeven.HilbertAffineChange
import TranslatedDepthSeven.PilaFiveDimensionalHighDegree
import TranslatedDepthSeven.PilaFiveDimensionalDegreeAtLeastThree
import TranslatedDepthSeven.AffineIntegralPointTransport
import TranslatedDepthSeven.FiniteFamilyHomogenization

/-!
# Pila after rational coefficient extension and packet rescaling

This file joins four literal algebraic facts needed for the low-rank branch.
A homogeneous geometrically prime ideal over `ℚ` stays homogeneous and prime
over `ℝ`; its projective Hilbert polynomial is unchanged; passage to the
affine cone cumulatively sums that polynomial; and the packet substitution
`x = x₀ + m z` preserves the resulting affine Hilbert polynomial.

The last theorem applies Pila's printed estimate to a projective fourfold of
degree at least eight.  No dimension or degree assertion after coefficient
extension is assumed separately.
-/

namespace TranslatedDepthSeven

noncomputable section

open Published

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluation of rational coefficients at a rational point commutes with
the coefficient embedding into `ℝ`. -/
theorem eval_realCoefficientExtension_at_rationalPoint
    {N : ℕ} (f : MvPolynomial (Fin N) ℚ) (x : Fin N → ℚ) :
    MvPolynomial.eval (fun i ↦ algebraMap ℚ ℝ (x i))
        (MvPolynomial.map (algebraMap ℚ ℝ) f) =
      algebraMap ℚ ℝ (MvPolynomial.eval x f) := by
  rw [← MvPolynomial.eval₂_eq_eval_map]
  simpa [MvPolynomial.eval₂_id] using
    (MvPolynomial.eval₂_comp_left (algebraMap ℚ ℝ)
      (RingHom.id ℚ) x f).symm

/-- A normalized integral displacement lies on the real packet transform
of a rational ideal whenever its affine image lies on the rational ideal.
This is an exact zero-locus identity, not a counting assertion. -/
theorem mem_realPacketZeroLocus_of_rationalAffineImage
    {N m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin N) ℚ))
    (x₀ z : IntVector N)
    (hz : (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
      affineIdealZeroLocus I) :
    (fun i ↦ (z i : ℝ)) ∈
      affineIdealZeroLocus
        ((I.map (MvPolynomial.map (algebraMap ℚ ℝ))).map
          (affinePolynomialChangeAlgEquiv
            (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
            (by exact_mod_cast hm.ne'))) := by
  change ((I.map (MvPolynomial.map (algebraMap ℚ ℝ))).map
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne'))) ≤
      RingHom.ker (MvPolynomial.eval (fun i ↦ (z i : ℝ)))
  rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  intro f hf
  change MvPolynomial.eval (fun i ↦ (z i : ℝ))
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne')
        (MvPolynomial.map (algebraMap ℚ ℝ) f)) = 0
  change MvPolynomial.aeval (fun i ↦ (z i : ℝ))
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne')
        (MvPolynomial.map (algebraMap ℚ ℝ) f)) = 0
  rw [aeval_affinePolynomialChange]
  have hpoint :
      (fun i ↦ (x₀ i : ℝ) + (m : ℝ) * (z i : ℝ)) =
        (fun i ↦ algebraMap ℚ ℝ
          (integralAffineMap x₀ z m i : ℚ)) := by
    funext i
    simp [integralAffineMap]
  rw [hpoint, MvPolynomial.aeval_map_algebraMap]
  change MvPolynomial.aeval
      ((algebraMap ℚ ℝ) ∘
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ))) f = 0
  rw [MvPolynomial.aeval_algebraMap_apply]
  have hzf := hz f hf
  change MvPolynomial.aeval
      (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) f = 0 at hzf
  rw [hzf, map_zero]

/-- Membership in the preceding zero locus, together with a strict box
bound, gives membership in Pila's literal finite point set. -/
theorem intPoint_mem_pilaIntegralPoints_realPacket
    {N m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin N) ℚ))
    (x₀ z : IntVector N) (B : ℝ)
    (hbox : ∀ i, |(z i : ℝ)| < B)
    (hz : (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
      affineIdealZeroLocus I) :
    z ∈ pilaIntegralPoints
      ((I.map (MvPolynomial.map (algebraMap ℚ ℝ))).map
        (affinePolynomialChangeAlgEquiv
          (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
          (by exact_mod_cast hm.ne'))) B := by
  classical
  rw [pilaIntegralPoints, Finset.mem_filter]
  refine ⟨?_, hbox, mem_realPacketZeroLocus_of_rationalAffineImage
    hm I x₀ z hz⟩
  rw [mem_integerSupNormBox_iff]
  intro i
  have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  have habs : ((z i).natAbs : ℝ) ≤ (⌈B⌉₊ : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (le_of_lt (hbox i)).trans hceil
  exact_mod_cast habs

/-- Exact affine-cone Hilbert certificate over `ℝ` after the packet
substitution, obtained from rational projective data. -/
theorem rationalProjectiveCone_packet_hasAffineHilbertDimensionDegree
    {N r d m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hgeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal I)
    (hprojective : HasProjectiveDimensionDegree I r d)
    (x₀ : IntVector (N + 1)) :
    HasAffineHilbertDimensionDegree
      ((I.map (MvPolynomial.map (algebraMap ℚ ℝ))).map
        (affinePolynomialChangeAlgEquiv
          (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
          (by exact_mod_cast hm.ne'))) (r + 1) d := by
  let Iℝ : Ideal (MvPolynomial (Fin (N + 1)) ℝ) :=
    I.map (MvPolynomial.map (algebraMap ℚ ℝ))
  have hhomogeneousℝ : Iℝ.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℝ) := by
    exact isHomogeneous_map_mvPolynomialMap
      (algebraMap ℚ ℝ) I hhomogeneous
  have hprimeℝ : Iℝ.IsPrime := by
    exact realCoefficientExtension_isPrime_of_geometricallyPrime
      I hgeometricallyPrime
  have hprojectiveℝ : HasProjectiveHilbertDimensionDegree Iℝ r d := by
    exact real_hasProjectiveHilbertDimensionDegree_of_rational I hprojective
  apply
    (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
      Iℝ (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne') (r + 1) d).2
  exact
    hasAffineHilbertDimensionDegree_of_homogeneous_hasProjectiveHilbertDimensionDegree
      Iℝ hhomogeneousℝ hprimeℝ r d hprojectiveℝ

/-- Direct Pila bound for every geometrically integral rational projective
fourfold of degree in `[8,D]`, after the literal packet substitution. -/
theorem pila1995_rationalProjectiveFourfold_packet_degreeAtLeastEight
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d m : ℕ), 8 ≤ d → d ≤ D → ∀ (hm : 0 < m),
        ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
          GeometricallyPrimeMvPolynomialIdeal I →
          HasProjectiveDimensionDegree I 4 d →
          ∀ (x₀ : IntVector (N + 1)) (B : ℝ), 1 < B →
            ((pilaIntegralPoints
              ((I.map (MvPolynomial.map (algebraMap ℚ ℝ))).map
                (affinePolynomialChangeAlgEquiv
                  (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
                  (by exact_mod_cast hm.ne')))
              B).card : ℝ) ≤ C * B ^ ((33 / 8 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    pila1995_affineDimensionAtMostFive_degreeAtLeastEight_boundedDegree
      hPila (N + 1) D ε hε
  refine ⟨C, hC, ?_⟩
  intro d m hd hdD hm I hhomogeneous hgeometricallyPrime hprojective x₀ B hB
  exact hbound 5 d (by omega) hd hdD _
    (rationalProjectiveCone_packet_hasAffineHilbertDimensionDegree
      hm I hhomogeneous hgeometricallyPrime hprojective x₀) B hB

/-- Finite-subset form of the preceding estimate.  The counted points are
the original normalized integral displacements; membership in the source
set of Pila's theorem is derived from their displayed rational affine
images. -/
theorem pila1995_finiteSet_rationalProjectiveFourfold_packet_degreeAtLeastEight
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d m : ℕ), 8 ≤ d → d ≤ D → ∀ (_hm : 0 < m),
        ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
          GeometricallyPrimeMvPolynomialIdeal I →
          HasProjectiveDimensionDegree I 4 d →
          ∀ (x₀ : IntVector (N + 1)) (B : ℝ), 1 < B →
            ∀ X : Finset (IntVector (N + 1)),
              (∀ z ∈ X, ∀ i, |(z i : ℝ)| < B) →
              (∀ z ∈ X,
                (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
                  affineIdealZeroLocus I) →
              (X.card : ℝ) ≤ C * B ^ ((33 / 8 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    pila1995_rationalProjectiveFourfold_packet_degreeAtLeastEight
      hPila N D ε hε
  refine ⟨C, hC, ?_⟩
  intro d m hd hdD hm I hhomogeneous hgeometricallyPrime hprojective
    x₀ B hB X hXbox hXzero
  let J : Ideal (MvPolynomial (Fin (N + 1)) ℝ) :=
    ((I.map (MvPolynomial.map (algebraMap ℚ ℝ))).map
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne')))
  have hsubset : X ⊆ pilaIntegralPoints J B := by
    intro z hz
    exact intPoint_mem_pilaIntegralPoints_realPacket
      hm I x₀ z B (hXbox z hz) (hXzero z hz)
  calc
    (X.card : ℝ) ≤ ((pilaIntegralPoints J B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ C * B ^ ((33 / 8 : ℝ) + ε) :=
      hbound d m hd hdD hm I hhomogeneous hgeometricallyPrime
        hprojective x₀ B hB

/-- The sharper split used in the final low-rank argument: Pila already
wins for every projective degree at least three. -/
theorem pila1995_rationalProjectiveFourfold_packet_degreeAtLeastThree
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d m : ℕ), 3 ≤ d → d ≤ D → ∀ (hm : 0 < m),
        ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
          GeometricallyPrimeMvPolynomialIdeal I →
          HasProjectiveDimensionDegree I 4 d →
          ∀ (x₀ : IntVector (N + 1)) (B : ℝ), 1 < B →
            ((pilaIntegralPoints
              ((I.map (MvPolynomial.map (algebraMap ℚ ℝ))).map
                (affinePolynomialChangeAlgEquiv
                  (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
                  (by exact_mod_cast hm.ne')))
              B).card : ℝ) ≤ C * B ^ ((13 / 3 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    pila1995_affineDimensionAtMostFive_degreeAtLeastThree_boundedDegree
      hPila (N + 1) D ε hε
  refine ⟨C, hC, ?_⟩
  intro d m hd hdD hm I hhomogeneous hgeometricallyPrime hprojective x₀ B hB
  exact hbound 5 d (by omega) hd hdD _
    (rationalProjectiveCone_packet_hasAffineHilbertDimensionDegree
      hm I hhomogeneous hgeometricallyPrime hprojective x₀) B hB

/-- Finite-subset version of the degree-at-least-three estimate. -/
theorem pila1995_finiteSet_rationalProjectiveFourfold_packet_degreeAtLeastThree
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d m : ℕ), 3 ≤ d → d ≤ D → ∀ (_hm : 0 < m),
        ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
          GeometricallyPrimeMvPolynomialIdeal I →
          HasProjectiveDimensionDegree I 4 d →
          ∀ (x₀ : IntVector (N + 1)) (B : ℝ), 1 < B →
            ∀ X : Finset (IntVector (N + 1)),
              (∀ z ∈ X, ∀ i, |(z i : ℝ)| < B) →
              (∀ z ∈ X,
                (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
                  affineIdealZeroLocus I) →
              (X.card : ℝ) ≤ C * B ^ ((13 / 3 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    pila1995_rationalProjectiveFourfold_packet_degreeAtLeastThree
      hPila N D ε hε
  refine ⟨C, hC, ?_⟩
  intro d m hd hdD hm I hhomogeneous hgeometricallyPrime hprojective
    x₀ B hB X hXbox hXzero
  let J : Ideal (MvPolynomial (Fin (N + 1)) ℝ) :=
    ((I.map (MvPolynomial.map (algebraMap ℚ ℝ))).map
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne')))
  have hsubset : X ⊆ pilaIntegralPoints J B := by
    intro z hz
    exact intPoint_mem_pilaIntegralPoints_realPacket
      hm I x₀ z B (hXbox z hz) (hXzero z hz)
  calc
    (X.card : ℝ) ≤ ((pilaIntegralPoints J B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ C * B ^ ((13 / 3 : ℝ) + ε) :=
      hbound d m hd hdD hm I hhomogeneous hgeometricallyPrime
        hprojective x₀ B hB

end

end TranslatedDepthSeven
