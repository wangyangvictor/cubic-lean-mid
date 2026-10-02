import TranslatedDepthSeven.DepthSevenNormalizedJacobianPartition
import TranslatedDepthSeven.DepthSevenPacketProjectiveSections
import TranslatedDepthSeven.CoefficientExtensionHomogeneousIdeal
import TranslatedDepthSeven.GradedLinearSubstitution
import TranslatedDepthSeven.JoinProjectionLinearSection
import TranslatedDepthSeven.StaticChartReservoirCover

/-!
# Rank-seven packets and their projected linear sections

This file joins the literal pieces of the normalized rank-seven argument.
Fix one of the finitely many Jacobian charts and one occupied residue packet
inside its chart cell.  If the square-free packet modulus is coprime to the
affine scale and to the value of that chart determinant at the packet base,
the tangent-minor argument puts the packet in a rational affine subspace of
dimension at most nine.  Integral Cramer equations then give four independent
homogeneous equations for the packet in `P^13`.

Under the linear map `[s:y] |-> [s*x_0 + m*y]`, those four equations have one
of two exact images: four independent equations if the projection vertex is
in their kernel, and three independent equations otherwise.  The theorem
below records both alternatives, point containment, and the elementary
coefficient and Plucker-height bounds.  It contains no geometric component
or counting hypothesis.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped LinearAlgebra.Projectivization
open Matrix MvPolynomial

set_option maxHeartbeats 6000000

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A coefficient bound which is uniform in the (at most nine) rational
directions selected from a normalized packet. -/
def depthSevenPacketSectionEntryBound (p : Parameters) : ℕ :=
  (13 * (2 * surfaceTangentNaturalSide p) + 1) *
    (Nat.factorial 9 * (4 * surfaceTangentNaturalSide p) ^ 9)

/-- The literal maximum absolute coordinate of the integral translation
base used in the join projection. -/
def depthSevenProjectionBaseHeight (x₀ : IntVector 13) : ℕ :=
  Finset.univ.sup fun j ↦ (x₀ j).natAbs

theorem coordinate_le_depthSevenProjectionBaseHeight
    (x₀ : IntVector 13) (j : Fin 13) :
    (x₀ j).natAbs ≤ depthSevenProjectionBaseHeight x₀ := by
  exact Finset.le_sup (f := fun i ↦ (x₀ i).natAbs) (Finset.mem_univ j)

/-- One fixed exponent dominating the three-equation image height. -/
def depthSevenProjectedSectionHeightExponent : ℕ := 260

theorem depthSevenPacketSectionEntryBound_cast_le
    (p : Parameters) :
    (depthSevenPacketSectionEntryBound p : ℝ) ≤ p.H ^ (39 : ℕ) := by
  let Tn := surfaceTangentNaturalSide p
  have hTn : (Tn : ℝ) ≤ 3 * p.H := by
    have h := surfaceTangentNaturalSide_cast_le_three_mul p
    change (Tn : ℝ) ≤ 3 * p.T at h
    nlinarith [p.T_le_H]
  have hH : (5 : ℝ) ≤ p.H := p.five_le_H
  have hfirst : (13 * (2 * Tn) + 1 : ℕ) ≤ (p.H ^ 4 : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hlinear : 26 * (Tn : ℝ) + 1 ≤ 79 * p.H := by
      nlinarith
    have h79 : (79 : ℝ) * p.H ≤ p.H ^ 4 := by
      calc
        (79 : ℝ) * p.H ≤ 5 ^ 3 * p.H := by
          gcongr
          norm_num
        _ ≤ p.H ^ 3 * p.H := by gcongr
        _ = p.H ^ 4 := by ring
    convert hlinear.trans h79 using 1
    all_goals ring
  have hfac : ((9 : ℕ).factorial : ℝ) ≤ p.H ^ 8 := by
    calc
      ((9 : ℕ).factorial : ℝ) ≤ 5 ^ 8 := by norm_num
      _ ≤ p.H ^ 8 := by gcongr
  norm_num [Nat.factorial] at hfac
  have hfourT : (4 * Tn : ℕ) ≤ (12 * p.H : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hpow : ((4 * Tn) ^ 9 : ℕ) ≤ (p.H ^ 27 : ℝ) := by
    norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    have hbasepow : (4 * (Tn : ℝ)) ^ 9 ≤ (12 * p.H) ^ 9 := by
      convert pow_le_pow_left₀ (by positivity) hfourT 9 using 1
      all_goals norm_num
    have hc : (12 : ℝ) ^ 9 ≤ 5 ^ 18 := by norm_num
    have hp : (5 : ℝ) ^ 18 ≤ p.H ^ 18 := by gcongr
    calc
      (4 * (Tn : ℝ)) ^ 9 ≤ (12 * p.H) ^ 9 := hbasepow
      _ = 12 ^ 9 * p.H ^ 9 := by ring
      _ ≤ p.H ^ 18 * p.H ^ 9 := by gcongr; exact hc.trans hp
      _ = p.H ^ 27 := by ring
  norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hpow
  rw [show depthSevenPacketSectionEntryBound p =
    (13 * (2 * Tn) + 1) * (Nat.factorial 9 * (4 * Tn) ^ 9) by
      rfl]
  norm_num only [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ p.H ^ 4 * (p.H ^ 8 * p.H ^ 27) := by gcongr
    _ = p.H ^ 39 := by ring

theorem depthSevenProjectionBaseHeight_cast_le
    (p : Parameters) (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (CF : ℕ) {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF) :
    (depthSevenProjectionBaseHeight x₀ : ℝ) ≤ p.H := by
  have hx₀data :=
    (mem_depthSevenTranslatedPointFinset_iff p equations CF x₀).mp hx₀
  have hbox := mem_integerSupNormBox_of_mem_translatedBox p x₀ hx₀data.1
  have hcoord : ∀ j, (x₀ j).natAbs ≤ ⌈p.B + p.L⌉₊ :=
    (mem_integerSupNormBox_iff x₀).mp hbox
  have hsup : depthSevenProjectionBaseHeight x₀ ≤ ⌈p.B + p.L⌉₊ := by
    apply Finset.sup_le
    intro j _hj
    exact hcoord j
  have hBL : 0 ≤ p.B + p.L := by nlinarith [p.hB, p.hL]
  have hceil : (⌈p.B + p.L⌉₊ : ℝ) < p.B + p.L + 1 :=
    Nat.ceil_lt_add_one hBL
  have hceilH : (⌈p.B + p.L⌉₊ : ℝ) ≤ p.H := by
    unfold Parameters.H
    have hm : (1 : ℝ) ≤ p.m := p.one_le_natCast_m
    linarith
  have hsupReal : (depthSevenProjectionBaseHeight x₀ : ℝ) ≤
      (⌈p.B + p.L⌉₊ : ℝ) := by
    exact_mod_cast hsup
  exact hsupReal.trans hceilH

/-- The explicit three-equation Plucker bound produced above is dominated
by one fixed power of the manuscript height. -/
theorem depthSeven_threeEquationHeightBound_le_ceil_heightPower
    (p : Parameters) (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (CF : ℕ) {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF) :
    Nat.factorial 3 *
        (2 * ((p.m + 13 * depthSevenProjectionBaseHeight x₀) *
          depthSevenPacketSectionEntryBound p) *
          depthSevenPacketSectionEntryBound p) ^ 3 ≤
      ⌈p.H ^ depthSevenProjectedSectionHeightExponent⌉₊ := by
  have hH : (5 : ℝ) ≤ p.H := p.five_le_H
  have hHnonneg : 0 ≤ p.H := p.H_pos.le
  have hm : (p.m : ℝ) ≤ p.H := by
    unfold Parameters.H
    nlinarith [p.hB, p.hL]
  have hx := depthSevenProjectionBaseHeight_cast_le p equations CF hx₀
  have hsum : ((p.m + 13 * depthSevenProjectionBaseHeight x₀ : ℕ) : ℝ) ≤
      p.H ^ 3 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hlinear : (p.m : ℝ) + 13 * depthSevenProjectionBaseHeight x₀ ≤
        14 * p.H := by nlinarith
    have h14 : (14 : ℝ) * p.H ≤ p.H ^ 3 := by
      have h14sq : (14 : ℝ) ≤ p.H ^ 2 := by nlinarith
      calc
        (14 : ℝ) * p.H ≤ p.H ^ 2 * p.H :=
          mul_le_mul_of_nonneg_right h14sq hHnonneg
        _ = p.H ^ 3 := by ring
    exact hlinear.trans h14
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hsum
  have hentry := depthSevenPacketSectionEntryBound_cast_le p
  have htwo : (2 : ℝ) ≤ p.H ^ 2 := by nlinarith
  have hinner :
      ((2 * ((p.m + 13 * depthSevenProjectionBaseHeight x₀) *
        depthSevenPacketSectionEntryBound p) *
        depthSevenPacketSectionEntryBound p : ℕ) : ℝ) ≤ p.H ^ 83 := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    calc
      2 * (((p.m : ℝ) + 13 * depthSevenProjectionBaseHeight x₀) *
          depthSevenPacketSectionEntryBound p) *
          depthSevenPacketSectionEntryBound p ≤
        2 * ((p.H ^ 3) * (p.H ^ 39)) * (p.H ^ 39) := by gcongr
      _ = 2 * p.H ^ 81 := by ring
      _ ≤ p.H ^ 2 * p.H ^ 81 :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = p.H ^ 83 := by ring
  have hfac : ((Nat.factorial 3 : ℕ) : ℝ) ≤ p.H ^ 2 := by
    norm_num only [Nat.factorial, Nat.cast_ofNat]
    nlinarith
  have hreal :
      (Nat.factorial 3 *
        (2 * ((p.m + 13 * depthSevenProjectionBaseHeight x₀) *
          depthSevenPacketSectionEntryBound p) *
          depthSevenPacketSectionEntryBound p) ^ 3 : ℕ) ≤
        (p.H ^ depthSevenProjectedSectionHeightExponent : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    calc
      _ ≤ p.H ^ 2 * (p.H ^ 83) ^ 3 := by
        exact mul_le_mul hfac
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hinner 3)
          (by positivity) (by positivity)
      _ = p.H ^ 251 := by ring
      _ ≤ p.H ^ depthSevenProjectedSectionHeightExponent := by
        unfold depthSevenProjectedSectionHeightExponent
        exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p.H) (by omega)
  exact_mod_cast hreal.trans
    (Nat.le_ceil (p.H ^ depthSevenProjectedSectionHeightExponent))

theorem ceil_projectedSectionHeightPower_le
    (p : Parameters) {CF : ℕ}
    (hCF : depthSevenProjectedSectionHeightExponent ≤ CF) :
    ⌈p.H ^ depthSevenProjectedSectionHeightExponent⌉₊ ≤ ⌈p.H ^ CF⌉₊ := by
  apply Nat.ceil_mono
  exact pow_le_pow_right₀ (p.one_le_T.trans p.T_le_H) hCF

/-- The affine zero locus of a homogeneous ideal is stable under scalar
multiplication.  This is stated for the literal standard grading. -/
theorem smul_mem_affineIdealZeroLocus_of_isHomogeneous
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    {x : σ → K} (hx : x ∈ affineIdealZeroLocus I) (a : K) :
    (fun i ↦ a * x i) ∈ affineIdealZeroLocus I := by
  intro f hf
  rw [← f.sum_homogeneousComponent]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hcomponent : MvPolynomial.homogeneousComponent d f ∈ I :=
    homogeneousComponent_mem_of_mem_homogeneousIdeal I hI hf d
  rw [eval_smul_of_isHomogeneous _ _ _ _
    (MvPolynomial.homogeneousComponent_isHomogeneous d f)]
  rw [hx _ hcomponent, mul_zero]

/-- Extending an integral common zero to `Qbar` and adjoining rational row
equations preserves literal common-zero membership. -/
theorem intCast_mem_geometricLinearSectionEquationFinset
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {c : ℕ} (D : Matrix (Fin c) (Fin 13) ℚ)
    (x : IntVector 13) (hzero : IntegralCommonZero equations x)
    (hD : Matrix.mulVec D (fun j ↦ (x j : ℚ)) = 0) :
    (fun j ↦ algebraMap ℚ Qbar (x j : ℚ)) ∈
      finiteAffineCommonZeroLocus
        (geometricLinearSectionEquationFinset equations D) := by
  classical
  intro g hg
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
  rcases Finset.mem_union.mp hf with hf | hf
  · obtain ⟨fInt, hfInt, rfl⟩ := Finset.mem_image.mp hf
    have hzQ : MvPolynomial.eval (fun j ↦ (x j : ℚ))
        (MvPolynomial.map (Int.castRingHom ℚ) fInt) = 0 := by
      rw [eval_map_intCast, hzero fInt hfInt, Int.cast_zero]
    calc
      MvPolynomial.eval (fun j ↦ algebraMap ℚ Qbar (x j : ℚ))
          (MvPolynomial.map (algebraMap ℚ Qbar)
            (MvPolynomial.map (Int.castRingHom ℚ) fInt)) =
          algebraMap ℚ Qbar
            (MvPolynomial.eval (fun j ↦ (x j : ℚ))
              (MvPolynomial.map (Int.castRingHom ℚ) fInt)) := by
            simpa only [Function.comp_apply] using
              (MvPolynomial.map_eval (algebraMap ℚ Qbar)
                (fun j ↦ (x j : ℚ))
                (MvPolynomial.map (Int.castRingHom ℚ) fInt)).symm
      _ = 0 := by simpa using congrArg (algebraMap ℚ Qbar) hzQ
  · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hf
    calc
      MvPolynomial.eval (fun j ↦ algebraMap ℚ Qbar (x j : ℚ))
          (MvPolynomial.map (algebraMap ℚ Qbar)
            (rationalMatrixRowLinearPolynomial D i)) =
          algebraMap ℚ Qbar
            (MvPolynomial.eval (fun j ↦ (x j : ℚ))
              (rationalMatrixRowLinearPolynomial D i)) := by
            simpa only [Function.comp_apply] using
              (MvPolynomial.map_eval (algebraMap ℚ Qbar)
                (fun j ↦ (x j : ℚ))
                (rationalMatrixRowLinearPolynomial D i)).symm
      _ = algebraMap ℚ Qbar
          (Matrix.mulVec D (fun j ↦ (x j : ℚ)) i) := by
        rw [eval_rationalMatrixRowLinearPolynomial]
      _ = 0 := by
        simpa using congrArg (algebraMap ℚ Qbar) (congrFun hD i)

/-- If the original integral equations are homogeneous, then every equation
in the geometric rational-linear section family is homogeneous. -/
theorem geometricLinearSectionEquationFinset_each_isHomogeneous
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    {c : ℕ} (D : Matrix (Fin c) (Fin 13) ℚ)
    {g : MvPolynomial (Fin 13) Qbar}
    (hg : g ∈ geometricLinearSectionEquationFinset equations D) :
    ∃ d : ℕ, g.IsHomogeneous d := by
  classical
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
  rcases Finset.mem_union.mp hf with hf | hf
  · obtain ⟨fInt, hfInt, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨d, hd⟩ := hhomogeneous fInt hfInt
    exact ⟨d, (hd.map _).map _⟩
  · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨1, (rationalMatrixRowLinearPolynomial_isHomogeneous D i).map _⟩

/-- Homogeneity of the rational ideal generated by the original equations
is enough to make the whole geometric section ideal homogeneous.  The
individual displayed generators need not themselves be homogeneous. -/
theorem geometricLinearSectionIdeal_isHomogeneous
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hI : (finiteEquationIdeal
      (rationalizedEquationFinset equations)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    {c : ℕ} (D : Matrix (Fin c) (Fin 13) ℚ) :
    (finiteEquationIdeal
      (geometricLinearSectionEquationFinset equations D)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar) := by
  have hrow : (finiteEquationIdeal
      (rationalMatrixRowLinearEquationFamily D)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) := by
    apply Ideal.homogeneous_span
    intro f hf
    rw [Finset.mem_coe, rationalMatrixRowLinearEquationFamily,
      Finset.mem_image] at hf
    obtain ⟨i, _hi, rfl⟩ := hf
    exact ⟨1, rationalMatrixRowLinearPolynomial_isHomogeneous D i⟩
  have hsection : (finiteEquationIdeal
      (rationalLinearSectionEquationFinset equations D)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) := by
    rw [rationalLinearSectionEquationFinset,
      finiteEquationIdeal_union_rowLinearEquationFamily]
    exact hI.sup hrow
  have heq : finiteEquationIdeal
        (geometricLinearSectionEquationFinset equations D) =
      (finiteEquationIdeal
        (rationalLinearSectionEquationFinset equations D)).map
          (MvPolynomial.map (algebraMap ℚ Qbar)) := by
    classical
    rw [geometricLinearSectionEquationFinset]
    unfold finiteEquationIdeal
    rw [Ideal.map_span, Finset.coe_image]
  rw [heq]
  exact isHomogeneous_map_mvPolynomialMap (algebraMap ℚ Qbar)
    (finiteEquationIdeal
      (rationalLinearSectionEquationFinset equations D)) hsection

/-- Every literal projective section component is prime. -/
theorem projectiveSectionComponent_isPrime
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {c : ℕ} (D : Matrix (Fin c) (Fin 13) ℚ)
    {Q : Ideal (MvPolynomial (Fin 13) Qbar)}
    (hQ : IsProjectiveSectionComponent equations D Q) : Q.IsPrime :=
  finiteEquationMinimalPrime_isPrime
    (geometricLinearSectionEquationFinset equations D) hQ.1

/-- If the original generated rational ideal is homogeneous, every literal
geometric section component is homogeneous, without requiring a homogeneous
choice of its displayed generators. -/
theorem projectiveSectionComponent_isHomogeneous
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hI : (finiteEquationIdeal
      (rationalizedEquationFinset equations)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    {c : ℕ} (D : Matrix (Fin c) (Fin 13) ℚ)
    {Q : Ideal (MvPolynomial (Fin 13) Qbar)}
    (hQ : IsProjectiveSectionComponent equations D Q) :
    Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar) := by
  apply isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
    (geometricLinearSectionIdeal_isHomogeneous equations hI D)
  exact (mem_finiteEquationMinimalPrimes_iff
    (geometricLinearSectionEquationFinset equations D) Q).mp hQ.1

/-- Every nonzero integral point satisfying the original equations and the
row equations of `D` lies on an actual geometric projective component of the
literal section. -/
theorem exists_projectiveSectionComponent_through_integralPoint
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : (finiteEquationIdeal
      (rationalizedEquationFinset equations)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    {c : ℕ} (D : Matrix (Fin c) (Fin 13) ℚ)
    (x : IntVector 13) (hx : x ≠ 0)
    (hzero : IntegralCommonZero equations x)
    (hD : Matrix.mulVec D (fun j ↦ (x j : ℚ)) = 0) :
    ∃ Q : Ideal (MvPolynomial (Fin 13) Qbar),
      IsProjectiveSectionComponent equations D Q ∧
      ProjectivePointVanishesOnGeometricIdeal Q
        (integralProjectiveClass x hx) := by
  classical
  let xbar : Fin 13 → Qbar :=
    fun j ↦ algebraMap ℚ Qbar (x j : ℚ)
  have hxbar : xbar ∈ finiteAffineCommonZeroLocus
      (geometricLinearSectionEquationFinset equations D) :=
    intCast_mem_geometricLinearSectionEquationFinset
      equations D x hzero hD
  obtain ⟨Q, hQthrough⟩ :=
    finiteEquationComponentsThroughPoint_nonempty_of_mem
      (geometricLinearSectionEquationFinset equations D) xbar hxbar
  have hQspec :=
    (mem_finiteEquationComponentsThroughPoint_iff
      (geometricLinearSectionEquationFinset equations D) xbar Q).mp
      hQthrough
  have hQhomogeneous : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar) :=
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
      (geometricLinearSectionIdeal_isHomogeneous equations hhomogeneous D)
      ((mem_finiteEquationMinimalPrimes_iff
        (geometricLinearSectionEquationFinset equations D) Q).mp hQspec.1)
  have hirrelevant : ¬ geometricIrrelevantCoordinateIdeal 13 ≤ Q := by
    intro hirr
    apply hx
    funext j
    have hX : MvPolynomial.X j ∈ Q := by
      apply hirr
      apply Ideal.subset_span
      exact Set.mem_range_self j
    have heval : MvPolynomial.eval xbar (MvPolynomial.X j) = 0 :=
      RingHom.mem_ker.mp (hQspec.2 hX)
    have hcast : algebraMap ℚ Qbar (x j : ℚ) = 0 := by
      simpa [xbar] using heval
    have hrat : (x j : ℚ) = 0 :=
      (map_eq_zero_iff (algebraMap ℚ Qbar)
        (FaithfulSMul.algebraMap_injective ℚ Qbar)).mp hcast
    exact_mod_cast hrat
  have hcomponent : IsProjectiveSectionComponent equations D Q :=
    ⟨hQspec.1, hirrelevant⟩
  have hdisplayed : xbar ∈ affineIdealZeroLocus Q := hQspec.2
  let xrat : Fin 13 → ℚ := fun j ↦ (x j : ℚ)
  have hxrat : xrat ≠ 0 := intCast_ne_zero hx
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℚ xrat hxrat
  have ha' : a • xrat = (integralProjectiveClass x hx).rep := by
    simpa only [integralProjectiveClass, xrat] using ha
  have hscaled := smul_mem_affineIdealZeroLocus_of_isHomogeneous
    Q hQhomogeneous hdisplayed (algebraMap ℚ Qbar (a : ℚ))
  have hrep : (fun i ↦ algebraMap ℚ Qbar
      ((integralProjectiveClass x hx).rep i)) =
      fun i ↦ algebraMap ℚ Qbar (a : ℚ) * xbar i := by
    funext i
    have hi := congrFun ha' i
    change algebraMap ℚ Qbar ((integralProjectiveClass x hx).rep i) = _
    rw [← hi]
    change algebraMap ℚ Qbar ((a : ℚ) * (x i : ℚ)) =
      algebraMap ℚ Qbar (a : ℚ) * algebraMap ℚ Qbar (x i : ℚ)
    exact map_mul (algebraMap ℚ Qbar) (a : ℚ) (x i : ℚ)
  refine ⟨Q, hcomponent, ?_⟩
  rw [ProjectivePointVanishesOnGeometricIdeal, hrep]
  exact hscaled

/-- Outside the literal exceptional locus, every geometric component through
the point of a codimension-four section has projective dimension at most one. -/
theorem codimensionFour_component_dimension_le_one_of_not_exceptional
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (heightBound : ℕ)
    (D : Matrix (Fin 4) (Fin 13) ℚ) (hDrank : D.rank = 4)
    (hDheight : rationalProjectiveLinearHeight D ≤ heightBound)
    (Q : Ideal (MvPolynomial (Fin 13) Qbar))
    (hcomponent : IsProjectiveSectionComponent equations D Q)
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (hxQ : ProjectivePointVanishesOnGeometricIdeal Q x)
    (hnot : ¬ MemDepthSevenExceptionalLocus equations heightBound x)
    {r d : ℕ} (hQ : HasGeometricProjectiveDimensionDegree Q r d) :
    r ≤ 1 := by
  by_contra hr
  apply hnot
  refine ⟨4, by omega, by omega, D, hDrank, hDheight, Q,
    hcomponent, ?_, hxQ⟩
  exact Or.inr ⟨rfl, r, d, hQ, by omega⟩

/-- Outside the literal exceptional locus, a geometric component through a
codimension-three section has dimension at most two; in dimension two its
degree is at least eight. -/
theorem codimensionThree_component_dimension_degree_of_not_exceptional
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (heightBound : ℕ)
    (D : Matrix (Fin 3) (Fin 13) ℚ) (hDrank : D.rank = 3)
    (hDheight : rationalProjectiveLinearHeight D ≤ heightBound)
    (Q : Ideal (MvPolynomial (Fin 13) Qbar))
    (hcomponent : IsProjectiveSectionComponent equations D Q)
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (hxQ : ProjectivePointVanishesOnGeometricIdeal Q x)
    (hnot : ¬ MemDepthSevenExceptionalLocus equations heightBound x)
    {r d : ℕ} (hQ : HasGeometricProjectiveDimensionDegree Q r d) :
    r ≤ 2 ∧ (r = 2 → 8 ≤ d) := by
  constructor
  · by_contra hr
    apply hnot
    refine ⟨3, by omega, by omega, D, hDrank, hDheight, Q,
      hcomponent, ?_, hxQ⟩
    exact Or.inl ⟨by omega, by omega, Or.inl ⟨r, d, hQ, by omega⟩⟩
  · intro hr
    by_contra hd
    apply hnot
    refine ⟨3, by omega, by omega, D, hDrank, hDheight, Q,
      hcomponent, ?_, hxQ⟩
    subst r
    exact Or.inl ⟨by omega, by omega, Or.inr ⟨d, hQ, by omega⟩⟩

/-- Component extraction and the complete nonexceptional conclusion for a
point of a displayed codimension-four section. -/
theorem exists_codimensionFour_component_through_normalizedPoint
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : (finiteEquationIdeal
      (rationalizedEquationFinset equations)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (D : Matrix (Fin 4) (Fin 13) ℚ)
    (hDrank : D.rank = 4)
    (hDheight : rationalProjectiveLinearHeight D ≤ ⌈p.H ^ CF⌉₊)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF)
    (hD : Matrix.mulVec D
      (fun j ↦ (integralAffineMap x₀ z p.m j : ℚ)) = 0) :
    ∃ hx : integralAffineMap x₀ z p.m ≠ 0,
      ∃ Q : Ideal (MvPolynomial (Fin 13) Qbar),
        IsProjectiveSectionComponent equations D Q ∧
        ProjectivePointVanishesOnGeometricIdeal Q
          (integralProjectiveClass (integralAffineMap x₀ z p.m) hx) ∧
        ∀ r d, HasGeometricProjectiveDimensionDegree Q r d → r ≤ 1 := by
  classical
  have hzdata := (Finset.mem_filter.mp hz).2
  dsimp only at hzdata
  obtain ⟨_hbox, hzero, hx, _hlinear, hnot⟩ := hzdata
  obtain ⟨Q, hcomponent, hxQ⟩ :=
    exists_projectiveSectionComponent_through_integralPoint
      equations hhomogeneous D (integralAffineMap x₀ z p.m) hx hzero hD
  refine ⟨hx, Q, hcomponent, hxQ, ?_⟩
  intro r d hQ
  exact codimensionFour_component_dimension_le_one_of_not_exceptional
    equations ⌈p.H ^ CF⌉₊ D hDrank hDheight Q hcomponent
      (integralProjectiveClass (integralAffineMap x₀ z p.m) hx) hxQ hnot hQ

/-- Component extraction and the complete nonexceptional conclusion for a
point of a displayed codimension-three section. -/
theorem exists_codimensionThree_component_through_normalizedPoint
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : (finiteEquationIdeal
      (rationalizedEquationFinset equations)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (D : Matrix (Fin 3) (Fin 13) ℚ)
    (hDrank : D.rank = 3)
    (hDheight : rationalProjectiveLinearHeight D ≤ ⌈p.H ^ CF⌉₊)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF)
    (hD : Matrix.mulVec D
      (fun j ↦ (integralAffineMap x₀ z p.m j : ℚ)) = 0) :
    ∃ hx : integralAffineMap x₀ z p.m ≠ 0,
      ∃ Q : Ideal (MvPolynomial (Fin 13) Qbar),
        IsProjectiveSectionComponent equations D Q ∧
        ProjectivePointVanishesOnGeometricIdeal Q
          (integralProjectiveClass (integralAffineMap x₀ z p.m) hx) ∧
        ∀ r d, HasGeometricProjectiveDimensionDegree Q r d →
          r ≤ 2 ∧ (r = 2 → 8 ≤ d) := by
  classical
  have hzdata := (Finset.mem_filter.mp hz).2
  dsimp only at hzdata
  obtain ⟨_hbox, hzero, hx, _hlinear, hnot⟩ := hzdata
  obtain ⟨Q, hcomponent, hxQ⟩ :=
    exists_projectiveSectionComponent_through_integralPoint
      equations hhomogeneous D (integralAffineMap x₀ z p.m) hx hzero hD
  refine ⟨hx, Q, hcomponent, hxQ, ?_⟩
  intro r d hQ
  exact codimensionThree_component_dimension_degree_of_not_exceptional
    equations ⌈p.H ^ CF⌉₊ D hDrank hDheight Q hcomponent
      (integralProjectiveClass (integralAffineMap x₀ z p.m) hx) hxQ hnot hQ

/-- The Cramer construction for a finite packet, strengthened to retain the
entry bound needed after projecting the translated join. -/
theorem exists_fourRow_projectiveSection_with_entry_bound
    (p : Parameters) (Z : Finset (IntVector 13)) (base : IntVector 13)
    (hbase : base ∈ Z) (A₀ : AffineSubspace ℚ (Fin 13 → ℚ))
    (hA₀dim : Module.finrank ℚ A₀.direction ≤ 9)
    (hA₀mem : ∀ z ∈ Z, (fun j ↦ (z j : ℚ)) ∈ A₀)
    (hbox : ∀ z ∈ Z, ∀ j,
      (z j).natAbs ≤ 2 * surfaceTangentNaturalSide p) :
    ∃ A : Matrix (Fin 4) (Fin 14) ℤ,
      (A.map ((↑) : ℤ → ℚ)).rank = 4 ∧
      (∀ z ∈ Z,
        Matrix.mulVec (A.map ((↑) : ℤ → ℚ))
          (rationalHomogeneousAffinePoint z) = 0) ∧
      (∀ i q, (A i q).natAbs ≤ depthSevenPacketSectionEntryBound p) ∧
      rationalProjectiveLinearHeight (A.map ((↑) : ℤ → ℚ)) ≤
        ⌈p.H ^ packetSectionHeightExponent⌉₊ := by
  have hcoord : ∀ z ∈ Z, ∀ j,
      (z j - base j).natAbs ≤ 4 * surfaceTangentNaturalSide p := by
    intro z hz j
    calc
      (z j - base j).natAbs ≤ (z j).natAbs + (base j).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ 2 * surfaceTangentNaturalSide p +
          2 * surfaceTangentNaturalSide p :=
        Nat.add_le_add (hbox z hz j) (hbox base hbase j)
      _ = 4 * surfaceTangentNaturalSide p := by omega
  obtain ⟨r, point, J, hr, hdet, hspan, hB⟩ :=
    exists_integralDifferenceBasis_with_pivot_of_affineSubspace
      Z base hbase A₀ hA₀dim hA₀mem hcoord
  let B := integralDifferenceMatrix base (fun i ↦ (point i).1)
  have hfour : 4 ≤ 13 - r := by omega
  let A := fourRowCramerAffineProjectiveSectionMatrix hfour base B J
  have hentry : ∀ i q, (A i q).natAbs ≤
      depthSevenPacketSectionEntryBound p := by
    intro i q
    have hraw := fourRowCramerAffineProjectiveSectionMatrix_entry_natAbs_le
      hfour base B J hB (hbox base hbase) i q
    apply hraw.trans
    unfold depthSevenPacketSectionEntryBound
    have hfac : r.factorial ≤ (9 : ℕ).factorial := Nat.factorial_le hr
    have hpow : (4 * surfaceTangentNaturalSide p) ^ r ≤
        (4 * surfaceTangentNaturalSide p) ^ 9 := by
      have hbasepos : 0 < 4 * surfaceTangentNaturalSide p :=
        Nat.mul_pos (by norm_num) (one_le_surfaceTangentNaturalSide p)
      exact Nat.pow_le_pow_right hbasepos hr
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hfac hpow)
  refine ⟨A,
    fourRowCramerAffineProjectiveSectionMatrix_rank
      hfour base B J hdet, ?_, hentry, ?_⟩
  · intro z hz
    exact (projectivization_mk_mem_rationalProjectiveLinearSpace_iff
      (A.map ((↑) : ℤ → ℚ)) (rationalHomogeneousAffinePoint z)
      (rationalHomogeneousAffinePoint_ne_zero z)).mp
        (finitePacket_mem_fourRowCramerAffineProjectiveSection_of_span_eq
          hfour Z base B J hspan ⟨z, hz⟩)
  · have hraw : rationalProjectiveLinearHeight (A.map ((↑) : ℤ → ℚ)) ≤
        Nat.factorial 4 *
          ((13 * (2 * surfaceTangentNaturalSide p) + 1) *
            (r.factorial *
              (4 * surfaceTangentNaturalSide p) ^ r)) ^ 4 := by
      exact fourRowCramerAffineProjectiveSectionMatrix_height_le
        hfour base B J hB (hbox base hbase)
    exact hraw.trans
      (codimensionFour_packetSectionHeight_le_ceil_heightPower p hr)

/-- A point of one selected chart cell makes the selected chart determinant
equal to the corresponding numerical Jacobian minor. -/
theorem chartDeterminantValue_eq_integralJacobianMinor
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (x : IntVector 13) :
    MvPolynomial.eval x C.determinant =
      integralJacobianMinor (indexedFinsetFamily equations)
        x C.rows C.cols := by
  exact eval_integralJacobianMinorPolynomial
    (indexedFinsetFamily equations) x C.rows C.cols

/-- Occupancy of a static reservoir cell supplies exactly the two
coprimality statements needed at the chosen base of the corresponding full
chart packet.  Coprimality of the chart determinant is independent of the
chosen lift of the occupied residue vector. -/
theorem occupiedReservoirCell_supplies_chartPacket_coprimality
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (q : ℕ)
    (rho : Fin 13 → ZMod q)
    (hrho : rho ∈ occupiedIntegralResidues q
      (rankSevenChartReservoirCell
        p x₀ equations CF C denominator q)) :
    ∃ hrhoFull : rho ∈ occupiedIntegralResidues q
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
      Nat.Coprime q p.m ∧
      Nat.Coprime q
        (MvPolynomial.eval
          (integralAffineMap x₀
            (integralResiduePacketBase
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF C) rho hrhoFull) p.m)
          C.determinant).natAbs := by
  classical
  obtain ⟨z, hzCell, hzrho⟩ := mem_occupiedIntegralResidues_iff.mp hrho
  obtain ⟨hzChart, hscale, hchart⟩ := Finset.mem_filter.mp hzCell
  have hrhoFull : rho ∈ occupiedIntegralResidues q
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) :=
    mem_occupiedIntegralResidues_iff.mpr ⟨z, hzChart, hzrho⟩
  let base := integralResiduePacketBase
    (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
      rho hrhoFull
  have hbase := integralResiduePacketBase_mem
    (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
      rho hrhoFull
  have hbaseRho : integralResidueVector base = rho :=
    (mem_integralResiduePacket_iff.mp hbase).2
  have hcoordinate : ∀ i,
      (integralAffineMap x₀ z p.m i : ZMod q) =
        (integralAffineMap x₀ base p.m i : ZMod q) := by
    intro i
    have hbaseCoord : (base i : ZMod q) = rho i := by
      exact congrFun hbaseRho i
    simp only [integralAffineMap, Int.cast_add, Int.cast_mul,
      Int.cast_natCast]
    rw [congrFun hzrho i, hbaseCoord]
  have hscale' : Nat.Coprime q (p.m * denominator.natAbs) := by
    simpa [Int.natAbs_mul] using hscale
  refine ⟨hrhoFull,
    hscale'.of_dvd_right (Nat.dvd_mul_right p.m denominator.natAbs), ?_⟩
  exact coprime_eval_natAbs_of_coordinate_cast_eq C.determinant
    (integralAffineMap x₀ z p.m)
    (integralAffineMap x₀ base p.m) hcoordinate hchart

/-- One occupied packet in a fixed rank-seven chart has an integral
codimension-four source section and, after the translated join projection,
an integral codimension-four or codimension-three image section.  Every
point of the packet lies in the displayed image kernel. -/
theorem exists_projectedSection_for_rankSevenChartPacket
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct P)
    (rho : Fin 13 → ZMod (primeProduct P))
    (hrho : rho ∈ occupiedIntegralResidues (primeProduct P)
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C))
    (hqm : Nat.Coprime (primeProduct P) p.m)
    (hqchart : Nat.Coprime (primeProduct P)
      (MvPolynomial.eval
        (integralAffineMap x₀
          (integralResiduePacketBase
            (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
            rho hrho) p.m)
        C.determinant).natAbs) :
    ∃ A : Matrix (Fin 4) (Fin 14) ℤ,
      (A.map ((↑) : ℤ → ℚ)).rank = 4 ∧
      (∀ z ∈ integralResiduePacket
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) rho,
        Matrix.mulVec (A.map ((↑) : ℤ → ℚ))
          (rationalHomogeneousAffinePoint z) = 0) ∧
      (∀ i q, (A i q).natAbs ≤ depthSevenPacketSectionEntryBound p) ∧
      rationalProjectiveLinearHeight (A.map ((↑) : ℤ → ℚ)) ≤
        ⌈p.H ^ packetSectionHeightExponent⌉₊ ∧
      ((integralTranslatedJoinVertexEvaluation A x₀ p.m = 0 ∧
          ((integralTranslatedJoinImageFourEquationMatrix A).map
            ((↑) : ℤ → ℚ)).rank = 4 ∧
          rationalProjectiveLinearHeight
              ((integralTranslatedJoinImageFourEquationMatrix A).map
                ((↑) : ℤ → ℚ)) ≤
            Nat.factorial 4 * (depthSevenPacketSectionEntryBound p) ^ 4 ∧
          ∀ z ∈ integralResiduePacket
              (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) rho,
            Matrix.mulVec
              ((integralTranslatedJoinImageFourEquationMatrix A).map
                ((↑) : ℤ → ℚ))
              (fun j ↦ (integralAffineMap x₀ z p.m j : ℚ)) = 0) ∨
        ∃ i₀ : Fin 4,
          integralTranslatedJoinVertexEvaluation A x₀ p.m i₀ ≠ 0 ∧
          ((integralTranslatedJoinImageThreeEquationMatrix A x₀ p.m i₀).map
            ((↑) : ℤ → ℚ)).rank = 3 ∧
          rationalProjectiveLinearHeight
              ((integralTranslatedJoinImageThreeEquationMatrix
                A x₀ p.m i₀).map ((↑) : ℤ → ℚ)) ≤
            Nat.factorial 3 *
              (2 * ((p.m + 13 * depthSevenProjectionBaseHeight x₀) *
                depthSevenPacketSectionEntryBound p) *
                depthSevenPacketSectionEntryBound p) ^ 3 ∧
          (∀ z ∈ integralResiduePacket
              (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) rho,
            Matrix.mulVec
              ((integralTranslatedJoinImageThreeEquationMatrix
                A x₀ p.m i₀).map ((↑) : ℤ → ℚ))
              (fun j ↦ (integralAffineMap x₀ z p.m j : ℚ)) = 0)) := by
  let Z := depthSevenNormalizedJacobianChartCell p x₀ equations CF C
  let base := integralResiduePacketBase Z rho hrho
  have hqpos : 0 < primeProduct P :=
    Nat.pos_of_ne_zero (primeProduct_ne_zero hprime)
  have hqsf : Squarefree (primeProduct P) := primeProduct_squarefree hprime
  have hqthreshold : surfaceTangentQThreshold
      (surfaceTangentNaturalSide p) ≤ primeProduct P :=
    surfaceTangentQThreshold_le_of_normalized_reservoir_lower p hlower
  have hscale : ∀ s, s.Prime → s ∣ primeProduct P → ¬ s ∣ p.m := by
    intro s hs hsprod hsm
    exact (Nat.not_coprime_of_dvd_of_dvd hs.one_lt hsprod hsm) hqm
  have hqminor : Nat.Coprime (primeProduct P)
      (integralJacobianMinor (indexedFinsetFamily equations)
        (integralAffineMap x₀ base p.m) C.rows C.cols).natAbs := by
    rw [← chartDeterminantValue_eq_integralJacobianMinor equations C]
    exact hqchart
  have hrank : ∀ s, s.Prime → s ∣ primeProduct P →
      7 ≤ (jacobianMatrix (indexedFinsetFamily equations)
        (integralAffineMap x₀ base p.m) s).rank :=
    jacobian_rank_ge_for_prime_divisors_of_coprime_minor
      (indexedFinsetFamily equations)
      (integralAffineMap x₀ base p.m) C.rows C.cols hqminor
  have hzero : ∀ z ∈ Z,
      IntegralCommonZero equations (integralAffineMap x₀ z p.m) := by
    intro z hz
    exact depthSevenNormalized_integralCommonZero p x₀ equations CF
      ((mem_depthSevenNormalizedJacobianChartCell_iff
        p x₀ equations CF C z).mp hz).1
  have hbox : ∀ z ∈ Z, ∀ j,
      (z j).natAbs ≤ 2 * surfaceTangentNaturalSide p := by
    intro z hz
    exact depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
      p x₀ equations CF
        ((mem_depthSevenNormalizedJacobianChartCell_iff
          p x₀ equations CF C z).mp hz).1
  obtain ⟨A₀, hA₀dim, hA₀mem⟩ :=
    exists_surface_affineSubspace_for_occupied_packet
      equations x₀ p.m (primeProduct P) (surfaceTangentNaturalSide p) Z
      (one_le_surfaceTangentNaturalSide p) hqpos hqsf hqthreshold
      hzero hbox hscale rho hrho hrank
  have hbasePacket : base ∈ integralResiduePacket Z rho :=
    integralResiduePacketBase_mem Z rho hrho
  have hbaseZ : base ∈ Z :=
    (mem_integralResiduePacket_iff.mp hbasePacket).1
  obtain ⟨A, hArank, hAmem, hAentry, hAheight⟩ :=
    exists_fourRow_projectiveSection_with_entry_bound
      p (integralResiduePacket Z rho) base hbasePacket A₀ hA₀dim
      (by
        intro z hz
        exact hA₀mem z hz)
      (by
        intro z hz
        exact hbox z (mem_integralResiduePacket_iff.mp hz).1)
  refine ⟨A, hArank, hAmem, hAentry, hAheight, ?_⟩
  have hmInt : (p.m : ℤ) ≠ 0 := by exact_mod_cast p.hm.ne'
  rcases integralTranslatedJoinImage_rank_dichotomy
      A x₀ p.m hmInt hArank with hfour | hthree
  · left
    refine ⟨hfour.1, hfour.2, ?_, ?_⟩
    · exact integralTranslatedJoinImageFourEquationMatrix_height_le A hAentry
    · intro z hz
      have hzimage := integralTranslatedJoinImageFourEquationMatrix_mulVec_affinePoint
        A x₀ z p.m hmInt hfour.1 (hAmem z hz)
      simpa [integralAffineMap] using hzimage
  · obtain ⟨i₀, hpivot, hrankThree⟩ := hthree
    right
    refine ⟨i₀, hpivot, hrankThree, ?_, ?_⟩
    · apply integralTranslatedJoinImageThreeEquationMatrix_height_le
        A x₀ p.m i₀ hAentry
      · exact coordinate_le_depthSevenProjectionBaseHeight x₀
      · simp
    intro z hz
    have hzimage := integralTranslatedJoinImageThreeEquationMatrix_mulVec_affinePoint
      A x₀ z p.m hmInt i₀ hpivot (hAmem z hz)
    simpa [integralAffineMap] using hzimage

/-- Largest unconditional rank-seven packet assembly.  Starting from one
literal occupied chart packet, this theorem constructs the projected
codimension-four or codimension-three section, proves its height lies inside
the exceptional-locus cutoff, and extracts an actual geometric component
through every packet point.  Exclusion from the exceptional locus then gives
the exact dimension/degree alternatives used by the later counting step. -/
theorem exists_projectedSectionAndComponents_for_rankSevenChartPacket
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hCF : depthSevenProjectedSectionHeightExponent ≤ CF)
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF)
    (hhomogeneous : (finiteEquationIdeal
      (rationalizedEquationFinset equations)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct P)
    (rho : Fin 13 → ZMod (primeProduct P))
    (hrho : rho ∈ occupiedIntegralResidues (primeProduct P)
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C))
    (hqm : Nat.Coprime (primeProduct P) p.m)
    (hqchart : Nat.Coprime (primeProduct P)
      (MvPolynomial.eval
        (integralAffineMap x₀
          (integralResiduePacketBase
            (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
            rho hrho) p.m)
        C.determinant).natAbs) :
    (∃ D : Matrix (Fin 4) (Fin 13) ℚ,
        D.rank = 4 ∧
        rationalProjectiveLinearHeight D ≤ ⌈p.H ^ CF⌉₊ ∧
        ∀ z ∈ integralResiduePacket
            (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) rho,
          Matrix.mulVec D
            (fun j ↦ (integralAffineMap x₀ z p.m j : ℚ)) = 0 ∧
          ∃ hx : integralAffineMap x₀ z p.m ≠ 0,
            ∃ Q : Ideal (MvPolynomial (Fin 13) Qbar),
              IsProjectiveSectionComponent equations D Q ∧
              ProjectivePointVanishesOnGeometricIdeal Q
                (integralProjectiveClass
                  (integralAffineMap x₀ z p.m) hx) ∧
              ∀ r d, HasGeometricProjectiveDimensionDegree Q r d → r ≤ 1) ∨
      (∃ D : Matrix (Fin 3) (Fin 13) ℚ,
        D.rank = 3 ∧
        rationalProjectiveLinearHeight D ≤ ⌈p.H ^ CF⌉₊ ∧
        ∀ z ∈ integralResiduePacket
            (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) rho,
          Matrix.mulVec D
            (fun j ↦ (integralAffineMap x₀ z p.m j : ℚ)) = 0 ∧
          ∃ hx : integralAffineMap x₀ z p.m ≠ 0,
            ∃ Q : Ideal (MvPolynomial (Fin 13) Qbar),
              IsProjectiveSectionComponent equations D Q ∧
              ProjectivePointVanishesOnGeometricIdeal Q
                (integralProjectiveClass
                  (integralAffineMap x₀ z p.m) hx) ∧
              ∀ r d, HasGeometricProjectiveDimensionDegree Q r d →
                r ≤ 2 ∧ (r = 2 → 8 ≤ d)) := by
  classical
  obtain ⟨A, _hArank, _hAmem, _hAentry, _hAheight, hbranch⟩ :=
    exists_projectedSection_for_rankSevenChartPacket
      p x₀ equations CF C P hprime hlower rho hrho hqm hqchart
  rcases hbranch with hfour | hthree
  · left
    let D : Matrix (Fin 4) (Fin 13) ℚ :=
      (integralTranslatedJoinImageFourEquationMatrix A).map
        ((↑) : ℤ → ℚ)
    have hrawTo260 : Nat.factorial 4 *
        (depthSevenPacketSectionEntryBound p) ^ 4 ≤
        ⌈p.H ^ depthSevenProjectedSectionHeightExponent⌉₊ := by
      have h160 := codimensionFour_packetSectionHeight_le_ceil_heightPower
        p (r := 9) (by omega)
      have hbound260 : ⌈p.H ^ packetSectionHeightExponent⌉₊ ≤
          ⌈p.H ^ depthSevenProjectedSectionHeightExponent⌉₊ := by
        apply Nat.ceil_mono
        exact pow_le_pow_right₀ (p.one_le_T.trans p.T_le_H) (by
          norm_num [packetSectionHeightExponent,
            depthSevenProjectedSectionHeightExponent])
      have h160' : Nat.factorial 4 *
          (depthSevenPacketSectionEntryBound p) ^ 4 ≤
          ⌈p.H ^ packetSectionHeightExponent⌉₊ := by
        simpa [depthSevenPacketSectionEntryBound] using h160
      exact h160'.trans hbound260
    have hDheight : rationalProjectiveLinearHeight D ≤ ⌈p.H ^ CF⌉₊ :=
      hfour.2.2.1.trans <|
        hrawTo260.trans (ceil_projectedSectionHeightPower_le p hCF)
    refine ⟨D, hfour.2.1, hDheight, ?_⟩
    intro z hz
    have hDz := hfour.2.2.2 z hz
    refine ⟨hDz, ?_⟩
    have hzNormalized : z ∈
        depthSevenNormalizedDisplacementFinset p x₀ equations CF :=
      (mem_depthSevenNormalizedJacobianChartCell_iff
        p x₀ equations CF C z).mp
          (mem_integralResiduePacket_iff.mp hz).1 |>.1
    exact exists_codimensionFour_component_through_normalizedPoint
      p x₀ equations CF hhomogeneous D hfour.2.1 hDheight
        hzNormalized hDz
  · obtain ⟨i₀, _hpivot, hDrank, hraw, hmem⟩ := hthree
    right
    let D : Matrix (Fin 3) (Fin 13) ℚ :=
      (integralTranslatedJoinImageThreeEquationMatrix
        A x₀ p.m i₀).map ((↑) : ℤ → ℚ)
    have hDheight : rationalProjectiveLinearHeight D ≤ ⌈p.H ^ CF⌉₊ :=
      hraw.trans <|
        (depthSeven_threeEquationHeightBound_le_ceil_heightPower
          p equations CF hx₀).trans
          (ceil_projectedSectionHeightPower_le p hCF)
    refine ⟨D, hDrank, hDheight, ?_⟩
    intro z hz
    have hDz := hmem z hz
    refine ⟨hDz, ?_⟩
    have hzNormalized : z ∈
        depthSevenNormalizedDisplacementFinset p x₀ equations CF :=
      (mem_depthSevenNormalizedJacobianChartCell_iff
        p x₀ equations CF C z).mp
          (mem_integralResiduePacket_iff.mp hz).1 |>.1
    exact exists_codimensionThree_component_through_normalizedPoint
      p x₀ equations CF hhomogeneous D hDrank hDheight hzNormalized hDz

end

end TranslatedDepthSeven
