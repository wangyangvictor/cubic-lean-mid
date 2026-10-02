import TranslatedDepthSeven.LocalizedJacobianComponentMultiplicityOne
import TranslatedDepthSeven.IntegralSelectedJacobianCertificate
import TranslatedDepthSeven.LocalizedIdealEquality
import TranslatedDepthSeven.RationalPointLocalizedIdealEquality
import TranslatedDepthSeven.CharacteristicPolynomialHeight
import TranslatedDepthSeven.ExplicitDenominatorClearing
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Multiplicity one in every good reduction of an integral local chart

This file packages the exact specialization step needed for a fixed smooth
surface component.  The input is not a smoothness predicate or an effective
geometric interface.  It is a literal integral certificate:

* finitely many affine equations;
* one polynomial `u` on whose principal open those equations generate the
  displayed projective component;
* a choice of distinct Jacobian columns; and
* nonvanishing, at the marked integral point, of `u` and of that selected
  Jacobian determinant.

The product of the two displayed integer values is a single exceptional
integer.  At every prime not dividing it, coefficientwise reduction of the
same equations and the same principal-open certificate satisfies the
literal Hilbert--Samuel multiplicity predicate used in Salberger's theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

/-- Dehomogenization on `X₀ = 1`, over the integers. -/
def integralDehomogenizeAtZeroHom {N : ℕ} :
    MvPolynomial (Fin (N + 1)) ℤ →+* MvPolynomial (Fin N) ℤ := by
  let assignment : Fin (N + 1) → MvPolynomial (Fin N) ℤ :=
    Fin.cases 1 fun i ↦ MvPolynomial.X i
  exact (MvPolynomial.aeval assignment).toRingHom

/-- The same literal affine chart over the rationals. -/
def rationalDehomogenizeAtZeroHom {N : ℕ} :
    MvPolynomial (Fin (N + 1)) ℚ →+* MvPolynomial (Fin N) ℚ := by
  let assignment : Fin (N + 1) → MvPolynomial (Fin N) ℚ :=
    Fin.cases 1 fun i ↦ MvPolynomial.X i
  exact (MvPolynomial.aeval assignment).toRingHom

/-- Rational coefficient extension commutes with the literal affine chart. -/
theorem rationalDehomogenizeAtZeroHom_comp_map_intCast {N : ℕ} :
    (@rationalDehomogenizeAtZeroHom N).comp
        (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℚ)).comp
        (@integralDehomogenizeAtZeroHom N) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [rationalDehomogenizeAtZeroHom,
      integralDehomogenizeAtZeroHom]
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [rationalDehomogenizeAtZeroHom,
        integralDehomogenizeAtZeroHom]
    · simp [rationalDehomogenizeAtZeroHom,
        integralDehomogenizeAtZeroHom]

/-- Coefficientwise reduction commutes with the literal `X₀ = 1` chart. -/
theorem dehomogenizeAtZeroHom_comp_map_intCast
    {N p : ℕ} [Fact p.Prime] :
    (@dehomogenizeAtZeroHom N p inferInstance).comp
        (MvPolynomial.map (Int.castRingHom (ZMod p))) =
      (MvPolynomial.map (Int.castRingHom (ZMod p))).comp
        (@integralDehomogenizeAtZeroHom N) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [dehomogenizeAtZeroHom, integralDehomogenizeAtZeroHom]
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [dehomogenizeAtZeroHom, integralDehomogenizeAtZeroHom]
    · simp [dehomogenizeAtZeroHom, integralDehomogenizeAtZeroHom]

/-- Hence the affine chart of the reduced projective ideal is exactly the
reduction of the integral affine-chart ideal. -/
theorem standardAffineChartIdeal_map_intCast
    {N p : ℕ} [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin (N + 1)) ℤ)) :
    standardAffineChartIdeal
        (Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod p))) J) =
      Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod p)))
        (Ideal.map integralDehomogenizeAtZeroHom J) := by
  rw [standardAffineChartIdeal, Ideal.map_map, Ideal.map_map,
    dehomogenizeAtZeroHom_comp_map_intCast]

/-- The projective point `(1:z)` attached to an integral affine point. -/
def integralAffineProjectivePoint {N : ℕ} (z : Fin N → ℤ) :
    Fin (N + 1) → ℤ :=
  Fin.cases 1 z

@[simp]
theorem integralAffineProjectivePoint_zero {N : ℕ} (z : Fin N → ℤ) :
    integralAffineProjectivePoint z 0 = 1 := by
  rfl

@[simp]
theorem integralAffineProjectivePoint_succ {N : ℕ} (z : Fin N → ℤ)
    (i : Fin N) :
    integralAffineProjectivePoint z i.succ = z i := by
  rfl

/-- Reducing `(1:z)` and then taking the standard affine chart recovers the
coefficientwise reduction of `z`. -/
theorem standardAffineChartPoint_integralAffineProjectivePoint
    {N p : ℕ} [Fact p.Prime] (z : Fin N → ℤ) :
    standardAffineChartPoint
        (fun i ↦ (integralAffineProjectivePoint z i : ZMod p)) =
      fun i ↦ (z i : ZMod p) := by
  funext i
  simp [standardAffineChartPoint]

/-- Reduction of a displayed finite equation ideal is the ideal generated
by the coefficientwise reductions of the same indexed equations. -/
theorem map_span_range_mvPolynomial_map
    {R S : Type*} [CommRing R] [CommRing S]
    {N c : ℕ} (φ : R →+* S)
    (equations : Fin c → MvPolynomial (Fin N) R) :
    Ideal.map (MvPolynomial.map φ)
        (Ideal.span (Set.range equations)) =
      Ideal.span (Set.range fun i ↦ MvPolynomial.map φ (equations i)) := by
  rw [Ideal.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨equations i, ⟨i, rfl⟩, rfl⟩

/-- The exceptional integer has a completely elementary polynomial-height
bound.  In particular, once the equations and the principal-open polynomial
are fixed, its size is polynomial in the height of the marked point. -/
theorem integralSelectedJacobianChartCertificate_natAbs_le
    {N c Y : ℕ}
    (equations : Fin c → MvPolynomial (Fin N) ℤ)
    (selectedVar : Fin c → Fin N)
    (u : MvPolynomial (Fin N) ℤ) (z : Fin N → ℤ)
    (hz : ∀ i, (z i).natAbs ≤ Y) :
    let D := selectedJacobianDeterminant equations selectedVar
    (integralSelectedJacobianChartCertificate
        equations selectedVar u z).natAbs ≤
      (u.support.card * mvPolynomialCoefficientNatAbsMax u *
          max 1 Y ^ u.totalDegree) *
        (D.support.card * mvPolynomialCoefficientNatAbsMax D *
          max 1 Y ^ D.totalDegree) := by
  dsimp only [integralSelectedJacobianChartCertificate]
  rw [Int.natAbs_mul]
  apply Nat.mul_le_mul
  · exact eval_natAbs_le_support_mul_coeff_mul_pow_generic u z
      (fun _ hm ↦ coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax u hm)
      le_rfl hz
  · let D := selectedJacobianDeterminant equations selectedVar
    exact eval_natAbs_le_support_mul_coeff_mul_pow_generic D z
      (fun _ hm ↦ coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax D hm)
      le_rfl hz

noncomputable local instance integralPolynomialToRationalAlgebra {N : ℕ} :
    Algebra (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) ℚ) :=
  (MvPolynomial.map (Int.castRingHom ℚ)).toAlgebra

/-- The affine chart of the contracted integral model recovers exactly the
rational affine chart.  This is just localization contraction-extension and
commutation of coefficient extension with `X₀ = 1`. -/
theorem map_integralAffineChart_projectiveIntegralClosureIdeal
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
        (Ideal.map integralDehomogenizeAtZeroHom
          (projectiveIntegralClosureIdeal I)) =
      Ideal.map rationalDehomogenizeAtZeroHom I := by
  let R := MvPolynomial (Fin (N + 1)) ℤ
  let S := MvPolynomial (Fin (N + 1)) ℚ
  let M : Submonoid R :=
    (nonZeroDivisors ℤ).map (MvPolynomial.C : ℤ →+* R)
  letI : IsLocalization M S :=
    MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  rw [Ideal.map_map,
    ← rationalDehomogenizeAtZeroHom_comp_map_intCast,
    projectiveIntegralClosureIdeal]
  change Ideal.map
      (rationalDehomogenizeAtZeroHom.comp
        (MvPolynomial.map (Int.castRingHom ℚ)))
      (Ideal.comap (MvPolynomial.map (Int.castRingHom ℚ)) I) =
    Ideal.map rationalDehomogenizeAtZeroHom I
  rw [← Ideal.map_map]
  have hcontract := IsLocalization.map_comap M S I
  change Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
      (Ideal.comap (MvPolynomial.map (Int.castRingHom ℚ)) I) = I at hcontract
  rw [hcontract]

/-- An integral affine point on the rational component lies on the integral
affine chart of its contracted projective model. -/
theorem integralAffineChart_point_of_rationalProjectivePoint
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (z : Fin N → ℤ)
    (hz : ∀ f ∈ Ideal.map rationalDehomogenizeAtZeroHom I,
      MvPolynomial.eval (fun i ↦ (z i : ℚ)) f = 0) :
    ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I),
      MvPolynomial.eval z f = 0 := by
  intro f hf
  have hfQ : MvPolynomial.map (Int.castRingHom ℚ) f ∈
      Ideal.map rationalDehomogenizeAtZeroHom I := by
    rw [← map_integralAffineChart_projectiveIntegralClosureIdeal I]
    exact Ideal.mem_map_of_mem _ hf
  have heval := hz _ hfQ
  rw [eval_map_intCast] at heval
  exact_mod_cast heval

/-- A rational generic-fibre clearing identity for a fixed integral model
can be cleared by one integral polynomial.  The proof chooses a finite
generating family of `J`, clears one constant denominator for each generator,
and takes the literal product.  Thus the output is an ordinary principal-open
polynomial and not an abstract effectivity assertion. -/
theorem exists_integral_principalOpen_of_rational_mul_mem
    {N : ℕ}
    (I J : Ideal (MvPolynomial (Fin N) ℤ))
    (u : MvPolynomial (Fin N) ℤ) (z : Fin N → ℤ)
    (hu : MvPolynomial.eval z u ≠ 0)
    (hrational : ∀ f ∈ J,
      MvPolynomial.map (Int.castRingHom ℚ) (u * f) ∈
        Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) I) :
    ∃ U : MvPolynomial (Fin N) ℤ,
      MvPolynomial.eval z U ≠ 0 ∧ ∀ f ∈ J, U * f ∈ I := by
  classical
  let R := MvPolynomial (Fin N) ℤ
  let S := MvPolynomial (Fin N) ℚ
  let M : Submonoid R :=
    (nonZeroDivisors ℤ).map (MvPolynomial.C : ℤ →+* R)
  letI : IsLocalization M S :=
    MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  obtain ⟨n, generators, hJ⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian J)
  have hdenominator : ∀ i : Fin n,
      ∃ d : ℤ, d ≠ 0 ∧
        (MvPolynomial.C d * u) * generators i ∈ I := by
    intro i
    have hgi : generators i ∈ J := by
      rw [← hJ]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hmap : algebraMap R S (u * generators i) ∈
        Ideal.map (algebraMap R S) I := by
      exact hrational (generators i) hgi
    obtain ⟨m, hmM, hmI⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff
        M S I (u * generators i)).mp hmap
    obtain ⟨d, hd, hdm⟩ := Submonoid.mem_map.mp hmM
    refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd, ?_⟩
    rw [← hdm] at hmI
    simpa only [mul_assoc] using hmI
  choose d hd hclear using hdenominator
  let denominators : Fin n → R := fun i ↦ MvPolynomial.C (d i) * u
  let U : R := ∏ i, denominators i
  have hUclear : ∀ f ∈ J, U * f ∈ I := by
    intro f hf
    apply prod_denominators_mul_mem_of_mem_span_range I generators denominators
      hclear
    change f ∈ Submodule.span R (Set.range generators)
    rw [hJ]
    exact hf
  have heach : ∀ i, MvPolynomial.eval z (denominators i) ≠ 0 := by
    intro i
    change MvPolynomial.eval z (MvPolynomial.C (d i) * u) ≠ 0
    simp only [map_mul, eval_C]
    exact mul_ne_zero (hd i) hu
  have hU : MvPolynomial.eval z U ≠ 0 := by
    change MvPolynomial.eval z (∏ i, denominators i) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _hi ↦ heach i
  exact ⟨U, hU, hUclear⟩

/-- A point of the integral affine chart remains a point after every prime
reduction. -/
theorem isPointOn_standardAffineChart_map_intCast
    {N p : ℕ} [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin (N + 1)) ℤ))
    (z : Fin N → ℤ)
    (hz : ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom J,
      MvPolynomial.eval z f = 0) :
    IsPointOnSpecialFiber
      (standardAffineChartIdeal
        (Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod p))) J))
      (standardAffineChartPoint
        (fun i ↦ (integralAffineProjectivePoint z i : ZMod p))) := by
  rw [standardAffineChartIdeal_map_intCast,
    standardAffineChartPoint_integralAffineProjectivePoint,
    IsPointOnSpecialFiber]
  intro f hf
  obtain ⟨g, hg, hgf⟩ :=
    (Ideal.mem_map_iff_of_surjective
      (MvPolynomial.map (Int.castRingHom (ZMod p)))
      (MvPolynomial.map_surjective _ ZMod.intCast_surjective)).mp hf
  subst f
  rw [RingHom.mem_ker]
  change MvPolynomial.eval (fun i ↦ (z i : ZMod p))
      (MvPolynomial.map (Int.castRingHom (ZMod p)) g) = 0
  rw [eval_map_intCast, hz g hg, Int.cast_zero]

/-- An integral local complete-intersection certificate specializes to
multiplicity one at every prime away from one explicit integer.

The equality of the two local ideals is recorded in the elementary form
`u * J₀ ⊆ (equations)`.  This form survives coefficientwise reduction
because `ℤ → ZMod p`, and therefore the induced polynomial map, is
surjective. -/
theorem hasHilbertSamuelMultiplicityAt_one_of_integral_localEquations
    {N c : ℕ}
    (J : Ideal (MvPolynomial (Fin (N + 1)) ℤ))
    (z : Fin N → ℤ)
    (equations : Fin c → MvPolynomial (Fin N) ℤ)
    (selectedVar : Fin c → Fin N)
    (hselected : Function.Injective selectedVar)
    (u : MvPolynomial (Fin N) ℤ)
    (hpoint : ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom J,
      MvPolynomial.eval z f = 0)
    (hIJ : Ideal.span (Set.range equations) ≤
      Ideal.map integralDehomogenizeAtZeroHom J)
    (hclear : ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom J,
      u * f ∈ Ideal.span (Set.range equations))
    (hu : MvPolynomial.eval z u ≠ 0)
    (hminor : MvPolynomial.eval z
      (selectedJacobianDeterminant equations selectedVar) ≠ 0) :
    let Δ : ℤ := integralSelectedJacobianChartCertificate
      equations selectedVar u z
    Δ ≠ 0 ∧
      ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
        HasHilbertSamuelMultiplicityAt hp
          (Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod p))) J)
          (fun i ↦ (integralAffineProjectivePoint z i : ZMod p))
          (N - c) 1 := by
  dsimp only
  let Δ : ℤ := integralSelectedJacobianChartCertificate
    equations selectedVar u z
  have hΔ : Δ ≠ 0 := mul_ne_zero hu hminor
  refine ⟨hΔ, ?_⟩
  intro p hp hpΔ
  letI : Fact p.Prime := ⟨hp⟩
  let φ : MvPolynomial (Fin N) ℤ →+*
      MvPolynomial (Fin N) (ZMod p) :=
    MvPolynomial.map (Int.castRingHom (ZMod p))
  let Jp : Ideal (MvPolynomial (Fin (N + 1)) (ZMod p)) :=
    Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod p))) J
  let Pp : Fin (N + 1) → ZMod p :=
    fun i ↦ (integralAffineProjectivePoint z i : ZMod p)
  let equationsp : Fin c → MvPolynomial (Fin N) (ZMod p) :=
    fun i ↦ φ (equations i)
  let up : MvPolynomial (Fin N) (ZMod p) := φ u
  have hPp : IsPointOnSpecialFiber
      (standardAffineChartIdeal Jp) (standardAffineChartPoint Pp) := by
    exact isPointOn_standardAffineChart_map_intCast J z hpoint
  have hchart : standardAffineChartIdeal Jp =
      Ideal.map φ (Ideal.map integralDehomogenizeAtZeroHom J) := by
    exact standardAffineChartIdeal_map_intCast J
  have hspan : Ideal.map φ (Ideal.span (Set.range equations)) =
      Ideal.span (Set.range equationsp) := by
    exact map_span_range_mvPolynomial_map
      (Int.castRingHom (ZMod p)) equations
  have hIJp : Ideal.span (Set.range equationsp) ≤
      standardAffineChartIdeal Jp := by
    rw [← hspan, hchart]
    exact Ideal.map_mono hIJ
  have hφsurj : Function.Surjective φ :=
    MvPolynomial.map_surjective _ ZMod.intCast_surjective
  have hclearp : ∀ f ∈ standardAffineChartIdeal Jp,
      up * f ∈ Ideal.span (Set.range equationsp) := by
    intro f hf
    rw [hchart] at hf
    obtain ⟨g, hg, hgf⟩ :=
      (Ideal.mem_map_iff_of_surjective φ hφsurj).mp hf
    subst f
    rw [← map_mul, ← hspan]
    exact Ideal.mem_map_of_mem φ (hclear g hg)
  obtain ⟨hupReduced, hminorReduced⟩ :=
    integralSelectedJacobianChartCertificate_nonvanishing
      hp equations selectedVar u z hpΔ
  have hup : MvPolynomial.aeval (standardAffineChartPoint Pp) up ≠ 0 := by
    rw [standardAffineChartPoint_integralAffineProjectivePoint]
    exact hupReduced
  have hminorp : MvPolynomial.aeval (standardAffineChartPoint Pp)
      (selectedJacobianDeterminant equationsp selectedVar) ≠ 0 := by
    rw [standardAffineChartPoint_integralAffineProjectivePoint]
    exact hminorReduced
  exact hasHilbertSamuelMultiplicityAt_one_of_local_equations_selectedJacobian
    hp Jp Pp hPp equationsp selectedVar hselected up hIJp hclearp hup hminorp

/-- Surface form of the preceding theorem.  With `N - 2` local equations
in `N` affine variables, every good reduction has Hilbert--Samuel
multiplicity one and local dimension two. -/
theorem hasHilbertSamuelMultiplicityAt_surface_one_of_integral_localEquations
    {N : ℕ} (hN : 2 ≤ N)
    (J : Ideal (MvPolynomial (Fin (N + 1)) ℤ))
    (z : Fin N → ℤ)
    (equations : Fin (N - 2) → MvPolynomial (Fin N) ℤ)
    (selectedVar : Fin (N - 2) → Fin N)
    (hselected : Function.Injective selectedVar)
    (u : MvPolynomial (Fin N) ℤ)
    (hpoint : ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom J,
      MvPolynomial.eval z f = 0)
    (hIJ : Ideal.span (Set.range equations) ≤
      Ideal.map integralDehomogenizeAtZeroHom J)
    (hclear : ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom J,
      u * f ∈ Ideal.span (Set.range equations))
    (hu : MvPolynomial.eval z u ≠ 0)
    (hminor : MvPolynomial.eval z
      (selectedJacobianDeterminant equations selectedVar) ≠ 0) :
    let Δ : ℤ := integralSelectedJacobianChartCertificate
      equations selectedVar u z
    Δ ≠ 0 ∧
      ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
        HasHilbertSamuelMultiplicityAt hp
          (Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod p))) J)
          (fun i ↦ (integralAffineProjectivePoint z i : ZMod p)) 2 1 := by
  simpa [Nat.sub_sub_self hN] using
    hasHilbertSamuelMultiplicityAt_one_of_integral_localEquations
      J z equations selectedVar hselected u hpoint hIJ hclear hu hminor

/-- Combined rational-to-integral surface specialization.  It is enough to
verify the local clearing identity after extension from `ℤ` to `ℚ` for one
integral polynomial `u`.  Finite generation clears the remaining rational
constant denominators into an integral polynomial `U`; the preceding theorem
then supplies one explicit integer excluding all bad reductions. -/
theorem exists_integralCertificate_surface_multiplicityOne_of_rational_mul_mem
    {N : ℕ} (hN : 2 ≤ N)
    (J : Ideal (MvPolynomial (Fin (N + 1)) ℤ))
    (z : Fin N → ℤ)
    (equations : Fin (N - 2) → MvPolynomial (Fin N) ℤ)
    (selectedVar : Fin (N - 2) → Fin N)
    (hselected : Function.Injective selectedVar)
    (u : MvPolynomial (Fin N) ℤ)
    (hpoint : ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom J,
      MvPolynomial.eval z f = 0)
    (hIJ : Ideal.span (Set.range equations) ≤
      Ideal.map integralDehomogenizeAtZeroHom J)
    (hrational : ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom J,
      MvPolynomial.map (Int.castRingHom ℚ) (u * f) ∈
        Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
          (Ideal.span (Set.range equations)))
    (hu : MvPolynomial.eval z u ≠ 0)
    (hminor : MvPolynomial.eval z
      (selectedJacobianDeterminant equations selectedVar) ≠ 0) :
    ∃ U : MvPolynomial (Fin N) ℤ,
      MvPolynomial.eval z U ≠ 0 ∧
      (∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom J,
        U * f ∈ Ideal.span (Set.range equations)) ∧
      let Δ : ℤ := integralSelectedJacobianChartCertificate
        equations selectedVar U z
      Δ ≠ 0 ∧
        ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
          HasHilbertSamuelMultiplicityAt hp
            (Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod p))) J)
            (fun i ↦ (integralAffineProjectivePoint z i : ZMod p)) 2 1 := by
  obtain ⟨U, hU, hUclear⟩ :=
    exists_integral_principalOpen_of_rational_mul_mem
      (Ideal.span (Set.range equations))
      (Ideal.map integralDehomogenizeAtZeroHom J) u z hu hrational
  refine ⟨U, hU, hUclear, ?_⟩
  exact hasHilbertSamuelMultiplicityAt_surface_one_of_integral_localEquations
    hN J z equations selectedVar hselected U hpoint hIJ hUclear hU hminor

/-- Contracted-model form of the complete specialization result.  All
rational component statements are made about the literal affine chart
`Ideal.map rationalDehomogenizeAtZeroHom I`; the conclusion uses exactly
`projectiveSpecialFiberIdeal I`, the special fibre occurring in the
published Salberger interface. -/
theorem exists_integralCertificate_projectiveSurface_multiplicityOne
    {N : ℕ} (hN : 2 ≤ N)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (z : Fin N → ℤ)
    (equations : Fin (N - 2) → MvPolynomial (Fin N) ℤ)
    (selectedVar : Fin (N - 2) → Fin N)
    (hselected : Function.Injective selectedVar)
    (u : MvPolynomial (Fin N) ℤ)
    (hpoint : ∀ f ∈ Ideal.map rationalDehomogenizeAtZeroHom I,
      MvPolynomial.eval (fun i ↦ (z i : ℚ)) f = 0)
    (hIJ : Ideal.span (Set.range equations) ≤
      Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I))
    (hclearRational : ∀ f ∈ Ideal.map rationalDehomogenizeAtZeroHom I,
      MvPolynomial.map (Int.castRingHom ℚ) u * f ∈
        Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
          (Ideal.span (Set.range equations)))
    (hu : MvPolynomial.eval z u ≠ 0)
    (hminor : MvPolynomial.eval z
      (selectedJacobianDeterminant equations selectedVar) ≠ 0) :
    ∃ U : MvPolynomial (Fin N) ℤ,
      MvPolynomial.eval z U ≠ 0 ∧
      (∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
          (projectiveIntegralClosureIdeal I),
        U * f ∈ Ideal.span (Set.range equations)) ∧
      let Δ : ℤ := integralSelectedJacobianChartCertificate
        equations selectedVar U z
      Δ ≠ 0 ∧
        ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
          HasHilbertSamuelMultiplicityAt hp
            (projectiveSpecialFiberIdeal I)
            (fun i ↦ (integralAffineProjectivePoint z i : ZMod p)) 2 1 := by
  have hpointIntegral :=
    integralAffineChart_point_of_rationalProjectivePoint I z hpoint
  have hclearIntegralGeneric :
      ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
          (projectiveIntegralClosureIdeal I),
        MvPolynomial.map (Int.castRingHom ℚ) (u * f) ∈
          Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
            (Ideal.span (Set.range equations)) := by
    intro f hf
    have hfQ : MvPolynomial.map (Int.castRingHom ℚ) f ∈
        Ideal.map rationalDehomogenizeAtZeroHom I := by
      rw [← map_integralAffineChart_projectiveIntegralClosureIdeal I]
      exact Ideal.mem_map_of_mem _ hf
    simpa only [map_mul] using
      hclearRational (MvPolynomial.map (Int.castRingHom ℚ) f) hfQ
  simpa only [projectiveSpecialFiberIdeal] using
    exists_integralCertificate_surface_multiplicityOne_of_rational_mul_mem
      hN (projectiveIntegralClosureIdeal I) z equations selectedVar hselected
        u hpointIntegral hIJ hclearIntegralGeneric hu hminor

end

end TranslatedDepthSeven
