import TranslatedDepthSeven.RankSevenDegreeOneProperStarGeometry
import TranslatedDepthSeven.PilaLowDimension
import TranslatedDepthSeven.RationalProjectiveConePila

/-!
# Componentwise counting for a proper singular star

This file attaches the two printed counting theorems to the literal
minimal-prime components constructed in
`RankSevenDegreeOneProperStarGeometry`.

There is no assumed count for a star or for a family of components.  Pila's
coefficient-uniform theorem is applied to a geometrically integral component
of projective dimension at most three.  Salberger's coefficient-uniform
affine theorem, through the already proved homogeneous projection bridge, is
applied to a geometrically integral projective fourfold of degree at least
four.  The remaining alternatives are stated literally: failure of geometric
integrality, and a geometrically integral fourfold of degree at most three.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 8000000

/-- The Hilbert-polynomial form of Pila's bounded-degree estimate up to a
fixed affine dimension `R`.
specialization of Pila's theorem.  This is the form naturally supplied by
extension of a rational projective component to `ℝ`; no Krull-dimension
comparison is inserted. -/
theorem pila1995_hilbertDimensionAtMost_boundedDegree
    (hPila : Pila1995TheoremA)
    (N R D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), n ≤ R → 1 ≤ d → d ≤ D →
        ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
          HasAffineHilbertDimensionDegree I n d →
          ∀ B : ℝ, 1 < B →
            ((pilaIntegralPoints I B).card : ℝ) ≤
              C * B ^ ((R : ℝ) + epsilon) := by
  let S : Finset (ℕ × ℕ) :=
    (Finset.range (R + 1)).product (Finset.Icc 1 D)
  let J := {j : ℕ × ℕ // j ∈ S}
  have hEach : ∀ j : J, ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
        HasAffineHilbertDimensionDegree I j.1.1 j.1.2 →
        ∀ B : ℝ, 1 < B →
          ((pilaIntegralPoints I B).card : ℝ) ≤
            C * B ^ ((j.1.1 : ℝ) + epsilon) := by
    intro j
    have hj : j.1.1 ∈ Finset.range (R + 1) ∧
        j.1.2 ∈ Finset.Icc 1 D := Finset.mem_product.mp j.2
    have hjd : 1 ≤ j.1.2 := (Finset.mem_Icc.mp hj.2).1
    obtain ⟨c, hc, hsource⟩ := hPila j.1.1 j.1.2 N hjd
    let C : ℝ := c * pilaConstant j.1.2 epsilon
    have hconstant : 0 < pilaConstant j.1.2 epsilon := by
      unfold pilaConstant
      positivity
    refine ⟨C, mul_pos hc hconstant, ?_⟩
    intro I hI B hB
    have hprinted := hsource I hI B hB
    have hfactor := pilaFactor_le_const_mul_rpow
      (d := (j.1.2 : ℝ)) (ε := epsilon) (H := B)
      (by positivity) hepsilon hB.le
    have hpower := pilaMainPower_le_dimensionPower
      (n := j.1.1) hjd hB.le
    have hproduct :
        B ^ ((j.1.1 : ℝ) - 1 + (j.1.2 : ℝ)⁻¹) *
            pilaFactor j.1.2 B ≤
          B ^ (j.1.1 : ℝ) *
            (pilaConstant j.1.2 epsilon * B ^ epsilon) := by
      exact mul_le_mul hpower hfactor
        (by unfold pilaFactor; positivity) (by positivity)
    calc
      ((pilaIntegralPoints I B).card : ℝ) ≤
          c * B ^ ((j.1.1 : ℝ) - 1 + (j.1.2 : ℝ)⁻¹) *
            pilaFactor j.1.2 B := by
        simpa [pilaFactor] using hprinted
      _ = c * (B ^ ((j.1.1 : ℝ) - 1 + (j.1.2 : ℝ)⁻¹) *
            pilaFactor j.1.2 B) := by ring
      _ ≤ c * (B ^ (j.1.1 : ℝ) *
            (pilaConstant j.1.2 epsilon * B ^ epsilon)) := by
        exact mul_le_mul_of_nonneg_left hproduct hc.le
      _ = C * B ^ ((j.1.1 : ℝ) + epsilon) := by
        rw [Real.rpow_add (by positivity : 0 < B)]
        simp only [C]
        ring
  choose c hc hbound using hEach
  let C : ℝ := 1 + ∑ j : J, c j
  have hC : 0 < C := by
    dsimp only [C]
    have : 0 ≤ ∑ j : J, c j :=
      Finset.sum_nonneg fun j _ ↦ (hc j).le
    linarith
  refine ⟨C, hC, ?_⟩
  intro n d hn hd hdD I hI B hB
  have hmem : (n, d) ∈ S := Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_Icc.mpr ⟨hd, hdD⟩⟩
  let j : J := ⟨(n, d), hmem⟩
  have hjbound := hbound j I (by simpa [j] using hI) B hB
  have hcSum : c j ≤ ∑ k : J, c k := by
    exact Finset.single_le_sum
      (fun k _ ↦ (hc k).le) (Finset.mem_univ j)
  have hcC : c j ≤ C := by
    dsimp only [C]
    linarith
  have hjbound' : ((pilaIntegralPoints I B).card : ℝ) ≤
      c j * B ^ ((n : ℝ) + epsilon) := by
    simpa [j] using hjbound
  have hcoefficient : c j * B ^ ((n : ℝ) + epsilon) ≤
      C * B ^ ((n : ℝ) + epsilon) :=
    mul_le_mul_of_nonneg_right hcC
      (Real.rpow_nonneg (by positivity) ((n : ℝ) + epsilon))
  have hpower : B ^ ((n : ℝ) + epsilon) ≤
      B ^ ((R : ℝ) + epsilon) := by
    apply Real.rpow_le_rpow_of_exponent_le hB.le
    have hnReal : (n : ℝ) ≤ R := by exact_mod_cast hn
    linarith
  exact hjbound'.trans <| hcoefficient.trans <|
    mul_le_mul_of_nonneg_left hpower hC.le

/-- The original dimension-four specialization. -/
theorem pila1995_hilbertDimensionAtMostFour_boundedDegree
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), n ≤ 4 → 1 ≤ d → d ≤ D →
        ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
          HasAffineHilbertDimensionDegree I n d →
          ∀ B : ℝ, 1 < B →
            ((pilaIntegralPoints I B).card : ℝ) ≤
              C * B ^ ((4 : ℝ) + epsilon) :=
  pila1995_hilbertDimensionAtMost_boundedDegree hPila N 4 D epsilon hepsilon

/-- Coefficient-uniform Pila for a finite set of normalized points on the
cone over a geometrically integral rational projective variety of dimension
at most `R`. The affine translation and dilation are literal; the radius
`M+1` is used only to convert a weak integral box bound into Pila's strict
real box bound. -/
theorem exists_uniform_normalizedProjectiveAtMost_pilaBound
    (hPila : Pila1995TheoremA)
    (N R D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r d m M : ℕ), r ≤ R → d ≤ D → 1 ≤ M →
        ∀ (hm : 0 < m)
          (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
          GeometricallyPrimeMvPolynomialIdeal I →
          HasProjectiveDimensionDegree I r d →
          ∀ (x₀ : IntVector (N + 1))
            (points : Finset (IntVector (N + 1))),
            (∀ z ∈ points, ∀ i, (z i).natAbs ≤ M) →
            (∀ z ∈ points,
              (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
                affineIdealZeroLocus I) →
            (points.card : ℝ) ≤
              C * ((M : ℝ) + 1) ^ ((R : ℝ) + 1 + epsilon) := by
  obtain ⟨C, hC, hbound⟩ :=
    pila1995_hilbertDimensionAtMost_boundedDegree
      hPila (N + 1) (R + 1) D epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro r d m M hr hdD hM hm I hIhom hIgeom hIprojective
    x₀ points hbox hzero
  let J : Ideal (MvPolynomial (Fin (N + 1)) ℝ) :=
    ((I.map (MvPolynomial.map (algebraMap ℚ ℝ))).map
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne')))
  have hd : 1 ≤ d :=
    projectiveDegree_pos_of_hasProjectiveDimensionDegree I r d hIprojective
  have hJ : HasAffineHilbertDimensionDegree J (r + 1) d := by
    exact rationalProjectiveCone_packet_hasAffineHilbertDimensionDegree
      hm I hIhom hIgeom hIprojective x₀
  have hB : (1 : ℝ) < (M : ℝ) + 1 := by
    have hNat : 1 < M + 1 := Nat.lt_succ_iff.mpr hM
    exact_mod_cast hNat
  have hsubset : points ⊆ pilaIntegralPoints J ((M : ℝ) + 1) := by
    intro z hz
    apply intPoint_mem_pilaIntegralPoints_realPacket hm I x₀ z
      ((M : ℝ) + 1)
    · intro i
      have hi : |(z i : ℝ)| ≤ (M : ℝ) := by
        simpa only [Int.cast_abs, Nat.cast_natAbs] using
          (show ((z i).natAbs : ℝ) ≤ (M : ℝ) by
            exact_mod_cast hbox z hz i)
      linarith
    · exact hzero z hz
  calc
    (points.card : ℝ) ≤
        ((pilaIntegralPoints J ((M : ℝ) + 1)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ C * ((M : ℝ) + 1) ^ ((R : ℝ) + 1 + epsilon) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        hbound (r + 1) d (by omega) hd hdD J hJ ((M : ℝ) + 1) hB

/-- Preserve the original dimension-three API. Taking `R = 2` in the
preceding theorem gives the sharper `3 + epsilon` needed for smooth stars. -/
theorem exists_uniform_normalizedProjectiveAtMostThree_pilaBound
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r d m M : ℕ), r ≤ 3 → d ≤ D → 1 ≤ M →
        ∀ (hm : 0 < m)
          (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
          GeometricallyPrimeMvPolynomialIdeal I →
          HasProjectiveDimensionDegree I r d →
          ∀ (x₀ : IntVector (N + 1))
            (points : Finset (IntVector (N + 1))),
            (∀ z ∈ points, ∀ i, (z i).natAbs ≤ M) →
            (∀ z ∈ points,
              (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
                affineIdealZeroLocus I) →
            (points.card : ℝ) ≤
              C * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
  simpa only [Nat.cast_ofNat, show (3 : ℝ) + 1 = 4 by norm_num] using
    exists_uniform_normalizedProjectiveAtMost_pilaBound
      hPila N 3 D epsilon hepsilon

/-- The exact static alternatives for one nonempty minimal component of a
proper singular star.  The first alternative is the geometric frontier
case.  In the geometrically integral case, either Pila applies in
projective dimension at most three, Salberger applies to a fourfold of
degree at least four, or the sole remaining piece is a fourfold of degree
at most three. -/
theorem nonvertexStar_minimalPrime_staticAlternatives
    (hHilbert : StandardAG.ProjectiveHilbertDegreeCertification ℚ)
    (hBezout : StandardAG.FiniteEquationProjectiveComponentBezoutBounds)
    (hstarVertex : StandardAG.ProjectiveStarEqualityForcesVertex)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (h : IntVector 13) (hh : h ≠ 0)
    (hzero : IntegralCommonZero equations h)
    (hnotVertex : ¬ LiesInGeometricProjectiveVertex h
      (rationalDepthSevenEquationIdeal equations))
    (hprime : (rationalDepthSevenEquationIdeal equations).IsPrime)
    (hdim : ringKrullDim
      (MvPolynomial (Fin 13) ℚ ⧸
        rationalDepthSevenEquationIdeal equations) = 6)
    (Q : Ideal (MvPolynomial (Fin 13) ℚ))
    (hQ : Q ∈ finiteMinimalPrimes
      (rationalProjectiveStarIdeal equations degree h))
    (x : Fin 13 → ℚ) (hxne : x ≠ 0)
    (hxQ : x ∈ affineIdealZeroLocus Q) :
    ∃ r d : ℕ,
      HasProjectiveDimensionDegree Q r d ∧
      r ≤ 4 ∧
      d ≤ max 1 (equationFamilyDegreeBound equations) ^ 13 ∧
      (¬ (qbarCoefficientExtensionIdeal Q).IsPrime ∨
        ((qbarCoefficientExtensionIdeal Q).IsPrime ∧ r ≤ 3) ∨
        ((qbarCoefficientExtensionIdeal Q).IsPrime ∧
          r = 4 ∧ d ≤ 3) ∨
        ((qbarCoefficientExtensionIdeal Q).IsPrime ∧
          r = 4 ∧ 4 ≤ d)) := by
  obtain ⟨r, d, hQprojective, hr⟩ :=
    nonvertexStar_minimalPrime_projectiveDimensionDegree
      hHilbert hstarVertex equations degree hdegree h hh hzero hnotVertex
        hprime hdim Q hQ x hxne hxQ
  have hd := (rationalProjectiveStar_componentBezoutBounds
    hBezout equations degree hdegree h).2 Q hQ r d hQprojective
  refine ⟨r, d, hQprojective, hr, hd, ?_⟩
  by_cases hgeom : (qbarCoefficientExtensionIdeal Q).IsPrime
  · by_cases hr3 : r ≤ 3
    · exact Or.inr (Or.inl ⟨hgeom, hr3⟩)
    · have hr4 : r = 4 := by omega
      by_cases hd3 : d ≤ 3
      · exact Or.inr (Or.inr (Or.inl ⟨hgeom, hr4, hd3⟩))
      · exact Or.inr (Or.inr (Or.inr
          ⟨hgeom, hr4, by omega⟩))
  · exact Or.inl hgeom

/-- In each of the two geometrically integral alternatives, the relevant
coefficient-uniform estimate is already available with its constants chosen
before the star centre and component.  This theorem deliberately keeps the
two displayed radii rather than concealing them in a new majorant. -/
theorem exists_uniform_properStarComponent_pila_salbergerBounds
    (hPila : Pila1995TheoremA)
    (hSalberger : Salberger2023Theorem04)
    (hProjection : StandardAG.BoundedDegreeHomogeneousProjectionMenu)
    (D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ K : ℕ, ∃ CP CS : ℝ, 0 < CP ∧ 0 < CS ∧
      (∀ (r d m M : ℕ), r ≤ 3 → d ≤ D → 1 ≤ M →
        ∀ (hm : 0 < m)
          (I : Ideal (MvPolynomial (Fin 13) ℚ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) →
          GeometricallyPrimeMvPolynomialIdeal I →
          HasProjectiveDimensionDegree I r d →
          ∀ (x₀ : IntVector 13) (points : Finset (IntVector 13)),
            (∀ z ∈ points, ∀ i, (z i).natAbs ≤ M) →
            (∀ z ∈ points,
              IsRationalConePoint I
                (intVectorToRat (integralAffineMap x₀ z m))) →
            (points.card : ℝ) ≤
              CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon)) ∧
      (∀ (d m M : ℕ), 4 ≤ d → d ≤ D → 0 < m →
        ∀ (I : Ideal (MvPolynomial (Fin 13) ℚ)) (hI : I.IsPrime),
          GeometricallyPrimeMvPolynomialIdeal I →
          I.IsHomogeneous
            (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) →
          ¬ projectiveIrrelevantIdeal ℚ 12 ≤ I →
          HasProjectiveDimensionDegree I 4 d →
          ∀ (x₀ : IntVector 13) (points : Finset (IntVector 13)),
            (∀ z ∈ points, ∀ i, (z i).natAbs ≤ M) →
            (∀ z ∈ points,
              IsRationalConePoint I
                (intVectorToRat (integralAffineMap x₀ z m))) →
            (points.card : ℝ) ≤
              CS * ((K * max 1 M : ℕ) : ℝ) ^
                ((4 : ℝ) + epsilon)) := by
  obtain ⟨CP, hCP, hPilaBound⟩ :=
    exists_uniform_normalizedProjectiveAtMostThree_pilaBound
      hPila 12 D epsilon hepsilon
  obtain ⟨K, CS, hCS, hSalbergerBound⟩ :=
    exists_uniform_normalizedProperFourfold_salbergerBound
      hSalberger hProjection 12 D (by omega) epsilon hepsilon
  refine ⟨K, CP, CS, hCP, hCS, ?_, ?_⟩
  · intro r d m M hr hdD hM hm I hIhom hIgeom hIprojective
      x₀ points hbox hzero
    exact hPilaBound r d m M hr hdD hM hm I hIhom hIgeom
      hIprojective x₀ points hbox (by
        intro z hz
        exact hzero z hz)
  · intro d m M hd hdD hm I hI hIgeom hIhom hIirrelevant
      hIprojective x₀ points hbox hzero
    exact hSalbergerBound I hI hIgeom hIhom hIirrelevant hIprojective
      hd hdD hm x₀ points hbox hzero

end

end TranslatedDepthSeven
