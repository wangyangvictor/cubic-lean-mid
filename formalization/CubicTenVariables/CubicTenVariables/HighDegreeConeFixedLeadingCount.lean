import CubicTenVariables.HomogeneousProgressionBoxCount
import CubicTenVariables.FixedLeadingHypersurfaceCountInduction
import TranslatedDepthSeven.BoundedAffineChartProjectionInternal
import TranslatedDepthSeven.HomogeneousProjectionMenuFromAffineInternal
import TranslatedDepthSeven.IntegralProjectiveConeBaseGeometryInternal

/-! Translated progression counts on fixed rational cones from a fixed-leading
hypersurface estimate. The existing internal projection theorem chooses a
single rational homogeneous image equation before any translation or modulus.
Only its scalar multiples occur as translated top parts. The literal target
count and the proved degree bound on projection fibres complete the transfer.
No Salberger input or family of saturated slicing certificates is used. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.HighDegreeConeFixedLeadingCount
open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingHypersurfaceCountInduction
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A fixed high-degree projective cone admits one uniform bound in every
translated and dilated displacement box. The projection is proved to exist;
no geometric projection hypothesis is supplied by the caller. The fixed-leading
hypersurface count is retained as an explicit argument. -/
theorem exists_normalized_bound
    {N r d : ℕ} {ε : ℝ}
    (hfixed : FixedRationalLeadingHypersurfaceBounds (r + 2) d ε)
    (hr : 1 ≤ r) (hrN : r < N)
    (I : Ideal (MvPolynomial (Fin (N+1)) ℚ)) (hI : I.IsPrime)
    (hgeom : GeometricallyPrimeMvPolynomialIdeal I)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N+1)) ℚ))
    (hdim : HasProjectiveDimensionDegree I r d) (hd : 4 ≤ d)
    (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (m : ℕ), 0 < m →
      ∀ (x₀ : Fin (N+1) → ℤ) (M : ℕ), 1 ≤ M →
      ∀ S : Finset (Fin (N+1) → ℤ),
      (∀ z ∈ S, ∀ i, (z i).natAbs ≤ M) →
      (∀ z ∈ S, IsRationalConePoint I
        (intVectorToRat (integralAffineMap x₀ z m))) →
      (S.card : ℝ) ≤ C*(M : ℝ)^((r : ℝ)+ε) := by
  classical
  have hirr : ¬ projectiveIrrelevantIdeal ℚ N ≤ I := by
    intro h
    have hz := ringKrullDim_quotient_eq_zero_of_irrelevant_le N I hI h
    have he := hdim.1
    rw [hz] at he
    have hp : (0 : WithBot ℕ∞) < (r : WithBot ℕ∞)+1 := by
      exact_mod_cast Nat.succ_pos r
    exact (ne_of_gt hp) he.symm
  have hmenu := boundedDegreeHomogeneousProjectionMenu_of_affineChart
    boundedDegreeAffineChartProjectionMenu_internal
  obtain ⟨menu,hmenu⟩ := hmenu N r d hrN
  obtain ⟨A,_hA,G,hproj⟩ := hmenu I hI hgeom hhom hirr d hdim le_rfl
  have hGhom : G.IsHomogeneous d := hproj.2.2.2.1
  have hGne : G ≠ 0 := hproj.2.2.2.2.1.ne_zero
  have hGabsolute : IsAbsolutelyIrreducible G := by
    apply absolutelyIrreducible_of_ker_eq_span_of_geometricallyPrime
      I hgeom (StandardAG.projectiveMatrixCoordinateMap I A) G hGne
    exact hproj.2.2.1
  obtain ⟨C₀,hC₀,hcount⟩ := hfixed G hGhom hGabsolute
  let K : ℕ := max 1 (rationalLinearProjectionNumeratorConstant A)
  let C : ℝ := max 1 ((d : ℝ)*C₀*(K : ℝ)^((r : ℝ)+ε))
  refine ⟨C,le_max_left _ _,?_⟩
  intro m hm x₀ M hM S hbox hzero
  have htop := integralTranslatedHomogeneousProjectionEquation_topPart
    I hI hgeom A G hproj x₀ hm
  have hden : (mvPolynomialRationalCommonDenominator G : ℚ) ≠ 0 := by
    exact_mod_cast (mvPolynomialRationalCommonDenominator_pos G).ne'
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hscalar : (mvPolynomialRationalCommonDenominator G : ℚ) * (m : ℚ) ^ d ≠ 0 :=
    mul_ne_zero hden (pow_ne_zero d hmQ)
  have htarget := hcount (integralTranslatedHomogeneousProjectionEquation A G x₀ m)
    ((mvPolynomialRationalCommonDenominator G : ℚ) * (m : ℚ) ^ d) hscalar htop.1
    (homogeneousProjectionImageRadius A M : ℝ)
    (by exact_mod_cast one_le_homogeneousProjectionImageRadius A M)
  have hcardNat : S.card ≤
      (affineHypersurfaceIntegerPoints
        (integralTranslatedHomogeneousProjectionEquation A G x₀ m)
        (homogeneousProjectionImageRadius A M : ℝ)).card * d :=
    finiteSet_card_le_index_card_mul_of_fibres S _
      (integralNumeratorLinearProjection A) d
      (fun z hz => integralNumeratorProjection_mem_translatedHypersurfacePoints
        I hI A G hproj x₀ z (hbox z hz) (hzero z hz))
      (fun y _ => integralNumeratorProjection_fibre_card_le_degree_of_homogeneousProjection
        I hI A G hproj hm x₀ S hzero y)
  have hexp : ((r + 2 : ℕ) : ℝ) - 2 + ε = (r : ℝ)+ε := by
    push_cast
    ring
  rw [hexp] at htarget
  have hc : (S.card : ℝ) ≤ ((d : ℝ)*C₀)*
      (homogeneousProjectionImageRadius A M : ℝ)^((r : ℝ)+ε) := by
    calc
      (S.card : ℝ) ≤
          ((affineHypersurfaceIntegerPoints
            (integralTranslatedHomogeneousProjectionEquation A G x₀ m)
            (homogeneousProjectionImageRadius A M : ℝ)).card : ℝ) * d := by
        exact_mod_cast hcardNat
      _ ≤ (C₀*(homogeneousProjectionImageRadius A M : ℝ)^((r : ℝ)+ε))*d :=
        mul_le_mul_of_nonneg_right htarget (Nat.cast_nonneg d)
      _ = _ := by ring
  have hrad : homogeneousProjectionImageRadius A M ≤ K*M := by
    apply max_le
    · exact le_trans (by simpa using hM) (Nat.mul_le_mul_right M (Nat.le_max_left _ _))
    · exact Nat.mul_le_mul_right M (Nat.le_max_right _ _)
  have hradR : (homogeneousProjectionImageRadius A M : ℝ) ≤ (K : ℝ)*(M : ℝ) := by
    exact_mod_cast hrad
  have hexp0 : 0 ≤ (r : ℝ)+ε := by positivity
  calc
    (S.card : ℝ) ≤ ((d : ℝ)*C₀)*(homogeneousProjectionImageRadius A M : ℝ)^((r : ℝ)+ε) := hc
    _ ≤ ((d : ℝ)*C₀)*((K : ℝ)*(M : ℝ))^((r : ℝ)+ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hradR hexp0) (mul_nonneg (Nat.cast_nonneg d) hC₀.le)
    _ = (((d : ℝ)*C₀)*(K : ℝ)^((r : ℝ)+ε))*(M : ℝ)^((r : ℝ)+ε) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring
    _ ≤ C*(M : ℝ)^((r : ℝ)+ε) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

/-- Literal real-centered progression bound for every finite set of actual
integral points on the rational cone, including the origin and box boundary. -/
theorem exists_bound
    {N r d : ℕ} {ε : ℝ}
    (hfixed : FixedRationalLeadingHypersurfaceBounds (r + 2) d ε)
    (hr : 1 ≤ r) (hrN : r < N)
    (I : Ideal (MvPolynomial (Fin (N+1)) ℚ)) (hI : I.IsPrime)
    (hgeom : GeometricallyPrimeMvPolynomialIdeal I)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N+1)) ℚ))
    (hdim : HasProjectiveDimensionDegree I r d) (hd : 4 ≤ d)
    (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : Finset (Fin (N+1) → ℤ))
      (u : Fin (N+1) → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin (N+1) → ℤ,
      (∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-b i) →
      (∀ x ∈ S, (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus I) →
      (S.card : ℝ) ≤ C*(1+L/(m : ℝ))^((r : ℝ)+ε) := by
  classical
  obtain ⟨C₀,hC₀,hcount⟩ := exists_normalized_bound hfixed hr hrN I hI hgeom hhom hdim hd hε
  let C : ℝ := C₀*2^((r : ℝ)+ε)
  have he : 0 ≤ (r : ℝ)+ε := by positivity
  have hC : 1 ≤ C := by
    exact one_le_mul_of_one_le_of_one_le hC₀ (Real.one_le_rpow (by norm_num) he)
  refine ⟨C,hC,?_⟩
  intro S u L hL m hm b hbox hres hzero
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hbase : 0 ≤ 1+L/(m : ℝ) := by positivity
  by_cases hS : S.Nonempty
  · obtain ⟨x₀,hx₀⟩ := hS
    let q := fun (x : Fin (N+1) → ℤ) i => (x i-x₀ i)/(m : ℤ)
    have hres₀ : ∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-x₀ i := by
      intro x hx i
      convert dvd_sub (hres x hx i) (hres x₀ hx₀ i) using 1
      ring
    obtain ⟨ha,hinj,hq⟩ := HomogeneousProgressionBoxCount.displacement_bound
      S u L m hm x₀ hx₀ hbox hres₀
    let M : ℕ := ⌈2*L/(m : ℝ)⌉₊+1
    have hc := hcount m hm x₀ M (by omega) (S.image q)
      (by intro z hz; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz; exact hq x hx)
      (by
        intro z hz
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
        rw [ha x hx]
        exact hzero x hx)
    rw [Finset.card_image_iff.mpr hinj] at hc
    have hM : (M : ℝ) ≤ 2*(1+L/(m : ℝ)) := by
      have ht := (Nat.ceil_lt_add_one (div_nonneg (by positivity : 0 ≤ 2*L) hmR.le)).le
      dsimp [M]
      push_cast
      rw [mul_div_assoc] at ht ⊢
      linarith
    calc
      (S.card : ℝ) ≤ C₀*(M : ℝ)^((r : ℝ)+ε) := hc
      _ ≤ C₀*(2*(1+L/(m : ℝ)))^((r : ℝ)+ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hM he) (by linarith)
      _ = C*(1+L/(m : ℝ))^((r : ℝ)+ε) := by
        rw [Real.mul_rpow (by norm_num) hbase]
        dsimp [C]
        ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hbase _)


/-- The source height factor absorbs the arbitrarily small exponent loss.
This retains a single constant before every translated progression. -/
theorem exists_source_bound
    {N r d : ℕ} {ε : ℝ}
    (hfixed : FixedRationalLeadingHypersurfaceBounds (r + 2) d ε)
    (hr : 1 ≤ r) (hrN : r < N)
    (I : Ideal (MvPolynomial (Fin (N+1)) ℚ)) (hI : I.IsPrime)
    (hgeom : GeometricallyPrimeMvPolynomialIdeal I)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N+1)) ℚ))
    (hdim : HasProjectiveDimensionDegree I r d) (hd : 4 ≤ d)
    (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : Finset (Fin (N+1) → ℤ))
      (u : Fin (N+1) → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin (N+1) → ℤ,
      (∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-b i) →
      (∀ x ∈ S, (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus I) →
      (S.card : ℝ) ≤ C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^r := by
  obtain ⟨C,hC,hcount⟩ := exists_bound hfixed hr hrN I hI hgeom hhom hdim hd hε
  refine ⟨C,hC,?_⟩
  intro S u L hL m hm b hbox hres hzero
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hb : 0 < 1+L/(m : ℝ) := by positivity
  have hLH : L/(m : ℝ) ≤ L := div_le_self hL hm1
  have hbH : 1+L/(m : ℝ) ≤ 2+‖u‖+L+(m : ℝ) := by
    linarith [norm_nonneg u]
  have hc := hcount S u L hL m hm b hbox hres hzero
  rw [Real.rpow_add hb, Real.rpow_natCast] at hc
  calc
    (S.card : ℝ) ≤ C*((1+L/(m : ℝ))^r*(1+L/(m : ℝ))^ε) := hc
    _ ≤ C*((1+L/(m : ℝ))^r*(2+‖u‖+L+(m : ℝ))^ε) := by
      gcongr
    _ = C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^r := by ring

end CubicTenVariables.HighDegreeConeFixedLeadingCount
