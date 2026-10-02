import TranslatedDepthSeven.CharacteristicPolynomialHeight
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.ZMod.Basic

/-!
# A literal coefficient controls the varying leading scalar

Suppose two integral polynomials become proportional over `ℚ`. Choosing a
nonzero coefficient `a` of the fixed polynomial and the corresponding
coefficient `b` of the varying polynomial gives the integral identity
`C a * f = C b * k`. In every field where `a * b` remains nonzero, the
reduction of `f` is the nonzero scalar multiple `(b / a) * k`.

For a homogeneous component of an integral polynomial `g`, the varying
integer `b` is bounded by the literal maximum coefficient size of `g`.
Neither integrality of the original rational scalar nor primitive
normalization is needed. All results are elementary algebra.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.FixedLeadingFormCoefficientReduction

open MvPolynomial

variable {σ : Type*}

/-- A nonzero rational proportionality scalar preserves a chosen nonzero
integral coefficient. -/
theorem coefficient_ne_zero_of_rational_const_mul
    {f k : MvPolynomial σ ℤ} {c : ℚ} {μ : σ →₀ ℕ}
    (h : map (Int.castRingHom ℚ) f = C c * map (Int.castRingHom ℚ) k)
    (hc : c ≠ 0) (ha : k.coeff μ ≠ 0) : f.coeff μ ≠ 0 := by
  have he := congrArg (coeff μ) h
  simp only [coeff_map, coeff_C_mul, Int.coe_castRingHom] at he
  have haQ : ((k.coeff μ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast ha
  intro hb
  rw [hb, Int.cast_zero] at he
  exact mul_ne_zero hc haQ he.symm

/-- Cross multiplication removes the rational scalar entirely. This even
holds when the scalar or the chosen coefficient is zero. -/
theorem integral_coefficient_cross_mul
    {f k : MvPolynomial σ ℤ} {c : ℚ} (μ : σ →₀ ℕ)
    (h : map (Int.castRingHom ℚ) f = C c * map (Int.castRingHom ℚ) k) :
    C (k.coeff μ) * f = C (f.coeff μ) * k := by
  have he (ν : σ →₀ ℕ) := congrArg (coeff ν) h
  simp only [coeff_map, coeff_C_mul, Int.coe_castRingHom] at he
  ext ν
  simp only [coeff_C_mul]
  have hQ : ((k.coeff μ : ℤ) : ℚ) * ((f.coeff ν : ℤ) : ℚ) =
      ((f.coeff μ : ℤ) : ℚ) * ((k.coeff ν : ℤ) : ℚ) := by
    rw [he ν, he μ]
    ring
  exact_mod_cast hQ

/-- Reduce the exact cross-multiplication identity in any field in which
the fixed coefficient does not vanish. -/
theorem map_eq_const_mul_of_cross_mul
    {K : Type*} [Field K] {f k : MvPolynomial σ ℤ} {a b : ℤ}
    (h : C a * f = C b * k) (ha : (a : K) ≠ 0) :
    map (Int.castRingHom K) f =
      C ((b : K) / (a : K)) * map (Int.castRingHom K) k := by
  ext ν
  have he := congrArg (coeff ν) (congrArg (map (Int.castRingHom K)) h)
  simp only [map_mul, map_C, coeff_C_mul, coeff_map, Int.coe_castRingHom] at he ⊢
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff ha).2 (by simpa only [mul_comm] using he)

/-- Nonzero scalar multiplication preserves irreducibility over the
reduction field. -/
theorem irreducible_map_of_cross_mul
    {K : Type*} [Field K] {f k : MvPolynomial σ ℤ} {a b : ℤ}
    (h : C a * f = C b * k) (ha : (a : K) ≠ 0) (hb : (b : K) ≠ 0)
    (hk : Irreducible (map (Int.castRingHom K) k)) :
    Irreducible (map (Int.castRingHom K) f) := by
  rw [map_eq_const_mul_of_cross_mul h ha]
  exact (irreducible_isUnit_mul
    ((isUnit_iff_ne_zero.mpr (div_ne_zero hb ha)).map C)).2 hk

/-- The same statement after any field extension, hence in particular
after passage to the algebraic closure. -/
theorem irreducible_extension_map_of_cross_mul
    {K L : Type*} [Field K] [Field L] (ι : K →+* L)
    {f k : MvPolynomial σ ℤ} {a b : ℤ}
    (h : C a * f = C b * k) (ha : (a : K) ≠ 0) (hb : (b : K) ≠ 0)
    (hk : Irreducible (map ι (map (Int.castRingHom K) k))) :
    Irreducible (map ι (map (Int.castRingHom K) f)) := by
  rw [map_eq_const_mul_of_cross_mul h ha, map_mul, map_C]
  have hs : ι ((b : K) / (a : K)) ≠ 0 := by
    exact fun hz => div_ne_zero hb ha (ι.injective (by simpa using hz))
  exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr hs).map C)).2 hk

/-- The distinguished coefficient of a homogeneous component is bounded
by the actual maximum absolute coefficient of the original polynomial. -/
theorem homogeneousComponent_coeff_natAbs_le
    (g : MvPolynomial σ ℤ) (d : ℕ) (μ : σ →₀ ℕ) :
    ((homogeneousComponent d g).coeff μ).natAbs ≤
      TranslatedDepthSeven.mvPolynomialCoefficientNatAbsMax g := by
  classical
  rw [coeff_homogeneousComponent]
  split_ifs
  · by_cases hμ : μ ∈ g.support
    · exact TranslatedDepthSeven.coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax g hμ
    · simp [notMem_support_iff.mp hμ]
  · simp

/-- The leading-component bridge packages the exact integral identity,
the nonzero varying coefficient, and its literal height bound. -/
theorem top_coefficient_certificate
    {g k : MvPolynomial σ ℤ} {d : ℕ} {c : ℚ} (μ : σ →₀ ℕ)
    (h : map (Int.castRingHom ℚ) (homogeneousComponent d g) =
      C c * map (Int.castRingHom ℚ) k)
    (hc : c ≠ 0) (ha : k.coeff μ ≠ 0) :
    (homogeneousComponent d g).coeff μ ≠ 0 ∧
      C (k.coeff μ) * homogeneousComponent d g =
        C ((homogeneousComponent d g).coeff μ) * k ∧
      ((homogeneousComponent d g).coeff μ).natAbs ≤
        TranslatedDepthSeven.mvPolynomialCoefficientNatAbsMax g := by
  exact ⟨coefficient_ne_zero_of_rational_const_mul h hc ha,
    integral_coefficient_cross_mul μ h,
    homogeneousComponent_coeff_natAbs_le g d μ⟩

private theorem map_homogeneousComponent
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (ρ : R →+* S) (g : MvPolynomial σ R) (d : ℕ) :
    map ρ (homogeneousComponent d g) = homogeneousComponent d (map ρ g) := by
  classical
  ext μ
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

/-- A nonvanishing coefficient product gives the actual reduced leading
component as an explicitly nonzero scalar multiple of the fixed form. -/
theorem top_reduction_of_coeff_product_ne_zero
    {K : Type*} [Field K] {g k : MvPolynomial σ ℤ} {d : ℕ} {c : ℚ}
    (μ : σ →₀ ℕ)
    (h : map (Int.castRingHom ℚ) (homogeneousComponent d g) =
      C c * map (Int.castRingHom ℚ) k)
    (hab : ((k.coeff μ * (homogeneousComponent d g).coeff μ : ℤ) : K) ≠ 0) :
    (((homogeneousComponent d g).coeff μ : ℤ) : K) / ((k.coeff μ : ℤ) : K) ≠ 0 ∧
      homogeneousComponent d (map (Int.castRingHom K) g) =
        C ((((homogeneousComponent d g).coeff μ : ℤ) : K) / ((k.coeff μ : ℤ) : K)) *
          map (Int.castRingHom K) k := by
  have hab' := mul_ne_zero_iff.mp (show
      ((k.coeff μ : ℤ) : K) * (((homogeneousComponent d g).coeff μ : ℤ) : K) ≠ 0 by
    simpa only [Int.cast_mul] using hab)
  refine ⟨div_ne_zero hab'.2 hab'.1, ?_⟩
  rw [← map_homogeneousComponent]
  exact map_eq_const_mul_of_cross_mul (integral_coefficient_cross_mul μ h) hab'.1

/-- Geometric irreducibility of the fixed reduced form transfers to the
actual homogeneous component of the reduced varying polynomial. -/
theorem geometrically_irreducible_top_reduction
    {K : Type*} [Field K] {g k : MvPolynomial σ ℤ} {d : ℕ} {c : ℚ}
    (μ : σ →₀ ℕ)
    (h : map (Int.castRingHom ℚ) (homogeneousComponent d g) =
      C c * map (Int.castRingHom ℚ) k)
    (hab : ((k.coeff μ * (homogeneousComponent d g).coeff μ : ℤ) : K) ≠ 0)
    (hk : Irreducible (map (algebraMap K (AlgebraicClosure K))
      (map (Int.castRingHom K) k))) :
    Irreducible (map (algebraMap K (AlgebraicClosure K))
      (homogeneousComponent d (map (Int.castRingHom K) g))) := by
  have hab' := mul_ne_zero_iff.mp (show
      ((k.coeff μ : ℤ) : K) * (((homogeneousComponent d g).coeff μ : ℤ) : K) ≠ 0 by
    simpa only [Int.cast_mul] using hab)
  rw [← map_homogeneousComponent]
  exact irreducible_extension_map_of_cross_mul (algebraMap K (AlgebraicClosure K))
    (integral_coefficient_cross_mul μ h) hab'.1 hab'.2 hk

/-- In characteristic `p`, the only new exclusion supplied by the varying
leading scalar is the prime divisibility of the literal coefficient `b`.
The other factor `a` belongs to the fixed polynomial. -/
theorem top_reduction_zmod_of_not_dvd_coeff_product
    {p : ℕ} [Fact p.Prime]
    {g k : MvPolynomial σ ℤ} {d : ℕ} {c : ℚ} (μ : σ →₀ ℕ)
    (h : map (Int.castRingHom ℚ) (homogeneousComponent d g) =
      C c * map (Int.castRingHom ℚ) k)
    (hab : ¬ (p : ℤ) ∣ k.coeff μ * (homogeneousComponent d g).coeff μ) :
    (((homogeneousComponent d g).coeff μ : ℤ) : ZMod p) / ((k.coeff μ : ℤ) : ZMod p) ≠ 0 ∧
      homogeneousComponent d (map (Int.castRingHom (ZMod p)) g) =
        C ((((homogeneousComponent d g).coeff μ : ℤ) : ZMod p) / ((k.coeff μ : ℤ) : ZMod p)) *
          map (Int.castRingHom (ZMod p)) k := by
  apply top_reduction_of_coeff_product_ne_zero μ h
  exact fun hz => hab ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz)

end CubicTenVariables.FixedLeadingFormCoefficientReduction
