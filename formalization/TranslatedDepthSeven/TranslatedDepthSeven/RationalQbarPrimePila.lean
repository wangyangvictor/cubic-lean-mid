import TranslatedDepthSeven.QbarPrimeAlgebraicCoefficientExtension
import TranslatedDepthSeven.HilbertAffineChange
import TranslatedDepthSeven.PilaFiveDimensionalHighDegree
import TranslatedDepthSeven.PilaFiveDimensionalDegreeAtLeastThree
import TranslatedDepthSeven.FiniteFamilyHomogenization
import TranslatedDepthSeven.AffineIntegralPointTransport
import TranslatedDepthSeven.NormalizationDegreeData

/-!
# Pila's theorem for rational ideals prime over Qbar

Pila's Theorem A may be stated directly for a rational affine variety
which is geometrically integral, with geometric integrality expressed by
primality of the literal coefficient extension to `Qbar`.  This is the
source-faithful rational specialization needed here.  It counts the same
integer vectors and uses the same real height as the usual real-coordinate
statement, but does not manufacture a real coefficient ideal.

The remainder of the file is internal: it proves that rational affine
coordinate changes preserve the `Qbar` prime test and the rational Hilbert
polynomial, and then specializes the printed exponent to projective
fourfolds of degree at least eight.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Published

/-- Integer points of strict affine height `< H` annihilating a rational
ideal, evaluated directly over `ℚ`. -/
def rationalPilaIntegralPoints {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℚ)) (H : ℝ) :
    Finset (IntVector N) := by
  classical
  exact (integerSupNormBox N ⌈H⌉₊).filter fun x ↦
    (∀ i, |(x i : ℝ)| < H) ∧
      ∀ f ∈ I, MvPolynomial.eval (fun i ↦ (x i : ℚ)) f = 0

/-- **Pila 1995, Theorem A, rational geometrically integral form.**
Geometric integrality is the literal assertion that the rational ideal
remains prime over `Qbar`.  This is a direct specialization of the printed
theorem, not an additional geometric or counting hypothesis. -/
def Pila1995TheoremARationalQbarPrime : Prop :=
  ∀ (n d N : ℕ), 1 ≤ d → ∃ c : ℝ, 0 < c ∧
    ∀ (I : Ideal (MvPolynomial (Fin N) ℚ)),
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
      HasAffineHilbertDimensionDegree I n d →
      ∀ H : ℝ, 1 < H →
        ((rationalPilaIntegralPoints I H).card : ℝ) ≤
          c * H ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) *
            Real.exp
              (12 * Real.sqrt
                ((d : ℝ) * Real.log H * Real.log (Real.log H)))

/-- **Pila 1995, Theorem A, linear-normalization degree form.**
Here the affine dimension and ordinary degree are given by a literal finite
injective homogeneous linear normalization: respectively its number of
parameters and its generic fraction-field rank.  The conclusion includes
an arbitrary invertible rational affine change, under which dimension and
degree are unchanged. -/
def Pila1995TheoremARationalQbarPrimeNormalization : Prop :=
  ∀ (n d N : ℕ), 1 ≤ d → ∃ c : ℝ, 0 < c ∧
    ∀ (I : Ideal (MvPolynomial (Fin N) ℚ)),
      I.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin N) ℚ) →
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
      ∀ (D : HomogeneousLinearNormalizationData I),
        D.parameterCount = n → D.genericRank = d →
        ∀ (y₀ : Fin N → ℚ) (r : ℚ) (hr : r ≠ 0) (H : ℝ), 1 < H →
          ((rationalPilaIntegralPoints
            (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)) H).card : ℝ) ≤
            c * H ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) *
              Real.exp
                (12 * Real.sqrt
                  ((d : ℝ) * Real.log H * Real.log (Real.log H)))

/-- Literal application of the rational geometrically integral form of
Pila's theorem. -/
theorem pila1995_rationalQbarPrime_apply
    (hPila : Pila1995TheoremARationalQbarPrime)
    {n d N : ℕ} (hd : 1 ≤ d)
    (I : Ideal (MvPolynomial (Fin N) ℚ))
    (hQbar :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hI : HasAffineHilbertDimensionDegree I n d) :
    ∃ c : ℝ, 0 < c ∧ ∀ H : ℝ, 1 < H →
      ((rationalPilaIntegralPoints I H).card : ℝ) ≤
        c * H ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) *
          Real.exp
            (12 * Real.sqrt
              ((d : ℝ) * Real.log H * Real.log (Real.log H))) := by
  obtain ⟨c, hc, hbound⟩ := hPila n d N hd
  exact ⟨c, hc, hbound I hQbar hI⟩

/-- Literal application of Pila's linear-normalization degree form. -/
theorem pila1995_rationalQbarPrimeNormalization_apply
    (hPila : Pila1995TheoremARationalQbarPrimeNormalization)
    {n d N : ℕ} (hd : 1 ≤ d)
    (I : Ideal (MvPolynomial (Fin N) ℚ))
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin N) ℚ))
    (hQbar :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (D : HomogeneousLinearNormalizationData I)
    (hparameters : D.parameterCount = n)
    (hrank : D.genericRank = d) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (y₀ : Fin N → ℚ) (r : ℚ) (hr : r ≠ 0)
        (H : ℝ), 1 < H →
        ((rationalPilaIntegralPoints
          (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)) H).card : ℝ) ≤
          c * H ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) *
            Real.exp
              (12 * Real.sqrt
                ((d : ℝ) * Real.log H * Real.log (Real.log H))) := by
  obtain ⟨c, hc, hbound⟩ := hPila n d N hd
  exact ⟨c, hc,
    hbound I hhomogeneous hQbar D hparameters hrank⟩

end Published

open Published

/-- The literal Qbar coefficient extension of a rational affine transform
is the corresponding Qbar affine transform of the coefficient extension. -/
theorem qbarCoefficientExtension_affinePolynomialChange
    {N : ℕ} (I : Ideal (MvPolynomial (Fin N) ℚ))
    (y₀ : Fin N → ℚ) (r : ℚ) (hr : r ≠ 0) :
    (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)).map
        (MvPolynomial.map (algebraMap ℚ Qbar)) =
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).map
        (affinePolynomialChangeAlgEquiv
          (fun i ↦ algebraMap ℚ Qbar (y₀ i))
          (algebraMap ℚ Qbar r)
          ((map_ne_zero (algebraMap ℚ Qbar)).2 hr)) := by
  exact map_map_affinePolynomialChangeAlgEquiv y₀ r hr I

/-- Hence the Qbar prime test is preserved by a rational affine
automorphism. -/
theorem qbarCoefficientExtension_affinePolynomialChange_isPrime
    {N : ℕ} (I : Ideal (MvPolynomial (Fin N) ℚ))
    (hQbar :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (y₀ : Fin N → ℚ) (r : ℚ) (hr : r ≠ 0) :
    ((I.map (affinePolynomialChangeAlgEquiv y₀ r hr)).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime := by
  rw [qbarCoefficientExtension_affinePolynomialChange I y₀ r hr]
  letI : (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime := hQbar
  exact Ideal.map_isPrime_of_equiv
    (affinePolynomialChangeAlgEquiv
      (fun i ↦ algebraMap ℚ Qbar (y₀ i))
      (algebraMap ℚ Qbar r)
      ((map_ne_zero (algebraMap ℚ Qbar)).2 hr))

/-- A rational zero of `I` at `x₀ + m z` is a rational zero of the
transformed ideal at `z`. -/
theorem mem_rationalPacketZeroLocus_of_rationalAffineImage
    {N m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin N) ℚ))
    (x₀ z : IntVector N)
    (hz : (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
      affineIdealZeroLocus I) :
    (fun i ↦ (z i : ℚ)) ∈
      affineIdealZeroLocus
        (I.map (affinePolynomialChangeAlgEquiv
          (fun i ↦ (x₀ i : ℚ)) (m : ℚ)
          (by exact_mod_cast hm.ne'))) := by
  change I.map (affinePolynomialChangeAlgEquiv
      (fun i ↦ (x₀ i : ℚ)) (m : ℚ)
      (by exact_mod_cast hm.ne')) ≤
    RingHom.ker (MvPolynomial.eval (fun i ↦ (z i : ℚ)))
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change MvPolynomial.aeval (fun i ↦ (z i : ℚ))
    (affinePolynomialChangeAlgEquiv
      (fun i ↦ (x₀ i : ℚ)) (m : ℚ)
      (by exact_mod_cast hm.ne') f) = 0
  rw [aeval_affinePolynomialChange]
  have hpoint :
      (fun i ↦ (x₀ i : ℚ) + (m : ℚ) * (z i : ℚ)) =
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) := by
    funext i
    simp [integralAffineMap]
  rw [hpoint]
  exact hz f hf

/-- Strict box membership and the preceding zero-locus identity give
membership in Pila's rational finite point set. -/
theorem intPoint_mem_rationalPilaIntegralPoints_packet
    {N m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin N) ℚ))
    (x₀ z : IntVector N) (B : ℝ)
    (hbox : ∀ i, |(z i : ℝ)| < B)
    (hz : (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
      affineIdealZeroLocus I) :
    z ∈ Published.rationalPilaIntegralPoints
      (I.map (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x₀ i : ℚ)) (m : ℚ)
        (by exact_mod_cast hm.ne'))) B := by
  classical
  rw [Published.rationalPilaIntegralPoints, Finset.mem_filter]
  refine ⟨?_, hbox,
    mem_rationalPacketZeroLocus_of_rationalAffineImage hm I x₀ z hz⟩
  rw [mem_integerSupNormBox_iff]
  intro i
  have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  have habs : ((z i).natAbs : ℝ) ≤ (⌈B⌉₊ : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (le_of_lt (hbox i)).trans hceil
  exact_mod_cast habs

/-- The rational affine cone and packet substitution have the required
Hilbert polynomial and pass the Qbar prime test, derived solely from the
displayed rational projective data. -/
theorem rationalProjectiveCone_packet_hasQbarPrimeAffineHilbertData
    {N r d m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hQbar :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hprojective : Published.HasProjectiveDimensionDegree I r d)
    (x₀ : IntVector (N + 1)) :
    let J := I.map (affinePolynomialChangeAlgEquiv
      (fun i ↦ (x₀ i : ℚ)) (m : ℚ)
      (by exact_mod_cast hm.ne'))
    (J.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime ∧
      Published.HasAffineHilbertDimensionDegree J (r + 1) d := by
  let hr : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  let J := I.map (affinePolynomialChangeAlgEquiv
    (fun i ↦ (x₀ i : ℚ)) (m : ℚ) hr)
  have hprime : I.IsPrime :=
    isPrime_of_qbarCoefficientExtension_isPrime I hQbar
  have hcone : Published.HasAffineHilbertDimensionDegree I (r + 1) d :=
    hasAffineHilbertDimensionDegree_of_homogeneous_hasProjectiveHilbertDimensionDegree
      I hhomogeneous hprime r d hprojective.toHilbert
  exact ⟨qbarCoefficientExtension_affinePolynomialChange_isPrime
      I hQbar (fun i ↦ (x₀ i : ℚ)) (m : ℚ) hr,
    (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
      I (fun i ↦ (x₀ i : ℚ)) (m : ℚ) hr (r + 1) d).2 hcone⟩

/-- A coefficient-uniform rational Pila estimate for homogeneous cones
with a displayed five-parameter linear normalization of generic rank in
`[3,D]`.  The generic rank is the ordinary degree appearing in Pila's
theorem: `HomogeneousLinearNormalizationData.exists_shiftedBinomialSqueeze`
identifies it as the leading binomial coefficient of the cumulative Hilbert
function. -/
theorem pila1995_rationalQbarPrimeNormalization_parameterFive_degreeAtLeastThree
    (hPila : Published.Pila1995TheoremARationalQbarPrimeNormalization)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ d : ℕ, 3 ≤ d → d ≤ D →
        ∀ (I : Ideal (MvPolynomial (Fin N) ℚ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin N) ℚ) →
          (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
          ∀ (D₀ : HomogeneousLinearNormalizationData I),
            D₀.parameterCount = 5 → D₀.genericRank = d →
            ∀ (y₀ : Fin N → ℚ) (r : ℚ) (hr : r ≠ 0)
              (B : ℝ), 1 < B →
              ((Published.rationalPilaIntegralPoints
                (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)) B).card : ℝ) ≤
                C * B ^ ((13 / 3 : ℝ) + ε) := by
  let S : Finset ℕ := Finset.Icc 3 D
  let index := {d : ℕ // d ∈ S}
  have hEach : ∀ j : index, ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℚ)),
        I.IsHomogeneous
            (MvPolynomial.homogeneousSubmodule (Fin N) ℚ) →
        (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        ∀ (D₀ : HomogeneousLinearNormalizationData I),
          D₀.parameterCount = 5 → D₀.genericRank = j.1 →
          ∀ (y₀ : Fin N → ℚ) (r : ℚ) (hr : r ≠ 0)
            (B : ℝ), 1 < B →
            ((Published.rationalPilaIntegralPoints
              (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)) B).card : ℝ) ≤
              C * B ^ ((13 / 3 : ℝ) + ε) := by
    intro j
    have hd : 3 ≤ j.1 := (Finset.mem_Icc.mp j.2).1
    obtain ⟨c, hc, hsource⟩ := hPila 5 j.1 N (by omega)
    let C : ℝ := c * pilaConstant j.1 ε
    refine ⟨C, mul_pos hc (by unfold pilaConstant; positivity), ?_⟩
    intro I hhomogeneous hQbar D₀ hparameters hrank y₀ r hr B hB
    have hprinted := hsource I hhomogeneous hQbar D₀ hparameters
      hrank y₀ r hr B hB
    have hfactor := pilaFactor_le_const_mul_rpow
      (d := (j.1 : ℝ)) (ε := ε) (H := B) (by positivity) hε hB.le
    have hmain := pilaMainPower_le_thirteenThirds
      (n := 5) (d := j.1) (B := B) (by omega) hd hB.le
    have hproduct :
        B ^ ((5 : ℝ) - 1 + (j.1 : ℝ)⁻¹) * pilaFactor j.1 B ≤
          B ^ (13 / 3 : ℝ) * (pilaConstant j.1 ε * B ^ ε) := by
      exact mul_le_mul hmain hfactor
        (by unfold pilaFactor; positivity) (by positivity)
    calc
      ((Published.rationalPilaIntegralPoints
          (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)) B).card : ℝ) ≤
          c * B ^ ((5 : ℝ) - 1 + (j.1 : ℝ)⁻¹) *
            pilaFactor j.1 B := by
        simpa [pilaFactor] using hprinted
      _ = c * (B ^ ((5 : ℝ) - 1 + (j.1 : ℝ)⁻¹) *
            pilaFactor j.1 B) := by ring
      _ ≤ c * (B ^ (13 / 3 : ℝ) *
            (pilaConstant j.1 ε * B ^ ε)) := by
        exact mul_le_mul_of_nonneg_left hproduct hc.le
      _ = C * B ^ ((13 / 3 : ℝ) + ε) := by
        rw [Real.rpow_add (by positivity : 0 < B)]
        simp only [C]
        ring
  choose c hc hbound using hEach
  let C : ℝ := 1 + ∑ j : index, c j
  have hC : 0 < C := by
    dsimp only [C]
    have hsum : 0 ≤ ∑ j : index, c j :=
      Finset.sum_nonneg fun j _ ↦ (hc j).le
    linarith
  refine ⟨C, hC, ?_⟩
  intro d hd hdD I hhomogeneous hQbar D₀ hparameters hrank y₀ r hr B hB
  have hmem : d ∈ S := Finset.mem_Icc.mpr ⟨hd, hdD⟩
  let j : index := ⟨d, hmem⟩
  have hjbound := hbound j I hhomogeneous hQbar D₀ hparameters
    (by simpa [j] using hrank) y₀ r hr B hB
  have hcSum : c j ≤ ∑ k : index, c k := by
    exact Finset.single_le_sum
      (fun k _ ↦ (hc k).le) (Finset.mem_univ j)
  have hcC : c j ≤ C := by
    dsimp only [C]
    linarith
  exact hjbound.trans
    (mul_le_mul_of_nonneg_right hcC (by positivity))

/-- Finite-subset form of the preceding normalization-degree estimate,
for the literal translated displacement packet. -/
theorem pila1995_finiteSet_rationalQbarPrimeNormalization_packet_degreeAtLeastThree
    (hPila : Published.Pila1995TheoremARationalQbarPrimeNormalization)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d m : ℕ), 3 ≤ d → d ≤ D → ∀ (_hm : 0 < m),
        ∀ (I : Ideal (MvPolynomial (Fin N) ℚ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin N) ℚ) →
          (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
          ∀ (D₀ : HomogeneousLinearNormalizationData I),
            D₀.parameterCount = 5 → D₀.genericRank = d →
            ∀ (x₀ : IntVector N) (B : ℝ), 1 < B →
              ∀ X : Finset (IntVector N),
                (∀ z ∈ X, ∀ i, |(z i : ℝ)| < B) →
                (∀ z ∈ X,
                  (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
                    affineIdealZeroLocus I) →
                (X.card : ℝ) ≤ C * B ^ ((13 / 3 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    pila1995_rationalQbarPrimeNormalization_parameterFive_degreeAtLeastThree
      hPila N D ε hε
  refine ⟨C, hC, ?_⟩
  intro d m hd hdD hm I hhomogeneous hQbar D₀ hparameters hrank
    x₀ B hB X hXbox hXzero
  let J := I.map (affinePolynomialChangeAlgEquiv
    (fun i ↦ (x₀ i : ℚ)) (m : ℚ)
    (by exact_mod_cast hm.ne'))
  have hsubset : X ⊆ Published.rationalPilaIntegralPoints J B := by
    intro z hz
    exact intPoint_mem_rationalPilaIntegralPoints_packet
      hm I x₀ z B (hXbox z hz) (hXzero z hz)
  calc
    (X.card : ℝ) ≤
        ((Published.rationalPilaIntegralPoints J B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ C * B ^ ((13 / 3 : ℝ) + ε) :=
      hbound d hd hdD I hhomogeneous hQbar D₀ hparameters hrank
        (fun i ↦ (x₀ i : ℚ)) (m : ℚ)
        (by exact_mod_cast hm.ne') B hB

/-- Direct Pila estimate for rational projective fourfold packets of degree
at least eight, with a coefficient-uniform constant over `d ≤ D`. -/
theorem pila1995_rationalQbarPrime_projectiveFourfold_packet_degreeAtLeastEight
    (hPila : Published.Pila1995TheoremARationalQbarPrime)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d m : ℕ), 8 ≤ d → d ≤ D → ∀ (hm : 0 < m),
        ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
          (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
          Published.HasProjectiveDimensionDegree I 4 d →
          ∀ (x₀ : IntVector (N + 1)) (B : ℝ), 1 < B →
            ((Published.rationalPilaIntegralPoints
              (I.map (affinePolynomialChangeAlgEquiv
                (fun i ↦ (x₀ i : ℚ)) (m : ℚ)
                (by exact_mod_cast hm.ne'))) B).card : ℝ) ≤
              C * B ^ ((33 / 8 : ℝ) + ε) := by
  let S : Finset (ℕ × ℕ) :=
    (Finset.range 6).product (Finset.Icc 8 D)
  let index := {j : ℕ × ℕ // j ∈ S}
  have hEach : ∀ j : index, ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
        (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        Published.HasAffineHilbertDimensionDegree I j.1.1 j.1.2 →
        ∀ B : ℝ, 1 < B →
          ((Published.rationalPilaIntegralPoints I B).card : ℝ) ≤
            C * B ^ ((33 / 8 : ℝ) + ε) := by
    intro j
    have hj := Finset.mem_product.mp j.2
    have hn : j.1.1 ≤ 5 := by
      have := Finset.mem_range.mp hj.1
      omega
    have hd : 8 ≤ j.1.2 := (Finset.mem_Icc.mp hj.2).1
    obtain ⟨c, hc, hsource⟩ := hPila j.1.1 j.1.2 (N + 1) (by omega)
    let C : ℝ := c * pilaConstant j.1.2 ε
    refine ⟨C, mul_pos hc (by unfold pilaConstant; positivity), ?_⟩
    intro I hQbar hI B hB
    have hprinted := hsource I hQbar hI B hB
    have hfactor := pilaFactor_le_const_mul_rpow
      (d := (j.1.2 : ℝ)) (ε := ε) (H := B) (by positivity) hε hB.le
    have hmain := pilaMainPower_le_thirtyThreeEighths hn hd hB.le
    have hproduct :
        B ^ ((j.1.1 : ℝ) - 1 + (j.1.2 : ℝ)⁻¹) * pilaFactor j.1.2 B ≤
          B ^ (33 / 8 : ℝ) *
            (pilaConstant j.1.2 ε * B ^ ε) := by
      exact mul_le_mul hmain hfactor
        (by unfold pilaFactor; positivity) (by positivity)
    calc
      ((Published.rationalPilaIntegralPoints I B).card : ℝ) ≤
          c * B ^ ((j.1.1 : ℝ) - 1 + (j.1.2 : ℝ)⁻¹) *
            pilaFactor j.1.2 B := by
        simpa [pilaFactor] using hprinted
      _ = c * (B ^ ((j.1.1 : ℝ) - 1 + (j.1.2 : ℝ)⁻¹) *
            pilaFactor j.1.2 B) := by ring
      _ ≤ c * (B ^ (33 / 8 : ℝ) *
            (pilaConstant j.1.2 ε * B ^ ε)) := by
        exact mul_le_mul_of_nonneg_left hproduct hc.le
      _ = C * B ^ ((33 / 8 : ℝ) + ε) := by
        rw [Real.rpow_add (by positivity : 0 < B)]
        simp only [C]
        ring
  choose c hc hbound using hEach
  let C : ℝ := 1 + ∑ j : index, c j
  have hC : 0 < C := by
    dsimp only [C]
    have hsum : 0 ≤ ∑ j : index, c j :=
      Finset.sum_nonneg fun j _ ↦ (hc j).le
    linarith
  refine ⟨C, hC, ?_⟩
  intro d m hd hdD hm I hhomogeneous hQbar hprojective x₀ B hB
  have hmem : (5, d) ∈ S := Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_Icc.mpr ⟨hd, hdD⟩⟩
  let j : index := ⟨(5, d), hmem⟩
  have hdata := rationalProjectiveCone_packet_hasQbarPrimeAffineHilbertData
    hm I hhomogeneous hQbar hprojective x₀
  have hjbound := hbound j _ hdata.1 (by simpa [j] using hdata.2) B hB
  have hcSum : c j ≤ ∑ k : index, c k := by
    exact Finset.single_le_sum
      (fun k _ ↦ (hc k).le) (Finset.mem_univ j)
  have hcC : c j ≤ C := by
    dsimp only [C]
    linarith
  exact hjbound.trans
    (mul_le_mul_of_nonneg_right hcC (by positivity))

/-- Finite-subset form for the literal normalized displacement points. -/
theorem pila1995_finiteSet_rationalQbarPrime_projectiveFourfold_packet_degreeAtLeastEight
    (hPila : Published.Pila1995TheoremARationalQbarPrime)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d m : ℕ), 8 ≤ d → d ≤ D → ∀ (_hm : 0 < m),
        ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
          (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
          Published.HasProjectiveDimensionDegree I 4 d →
          ∀ (x₀ : IntVector (N + 1)) (B : ℝ), 1 < B →
            ∀ X : Finset (IntVector (N + 1)),
              (∀ z ∈ X, ∀ i, |(z i : ℝ)| < B) →
              (∀ z ∈ X,
                (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
                  affineIdealZeroLocus I) →
              (X.card : ℝ) ≤ C * B ^ ((33 / 8 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    pila1995_rationalQbarPrime_projectiveFourfold_packet_degreeAtLeastEight
      hPila N D ε hε
  refine ⟨C, hC, ?_⟩
  intro d m hd hdD hm I hhomogeneous hQbar hprojective
    x₀ B hB X hXbox hXzero
  let J := I.map (affinePolynomialChangeAlgEquiv
    (fun i ↦ (x₀ i : ℚ)) (m : ℚ)
    (by exact_mod_cast hm.ne'))
  have hsubset : X ⊆ Published.rationalPilaIntegralPoints J B := by
    intro z hz
    exact intPoint_mem_rationalPilaIntegralPoints_packet
      hm I x₀ z B (hXbox z hz) (hXzero z hz)
  calc
    (X.card : ℝ) ≤
        ((Published.rationalPilaIntegralPoints J B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ C * B ^ ((33 / 8 : ℝ) + ε) :=
      hbound d m hd hdD hm I hhomogeneous hQbar hprojective x₀ B hB

end

end TranslatedDepthSeven
