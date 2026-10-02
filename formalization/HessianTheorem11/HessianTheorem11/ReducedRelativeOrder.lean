import HessianTheorem11.ReducedRelativeGeometry
import HessianTheorem11.ReducedWeightCurve

/-! The literal order of a closed target's ideal along a weighted orbit curve.
The curve is returned to the original coordinates before the target ideal is
tested.  Field conjugation preserves its pullbacks and their orders. -/
noncomputable section
namespace HessianTheorem11.ReducedRelative
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
open RationalDescent ReducedWeightCurve ReducedOrbitCoordinates
variable {K : Type*} [Field K] {n d : ℕ}

def conjugateSet (σ : K ≃+* K) (S : Set (MvPolynomial (Fin n) K)) :
    Set (MvPolynomial (Fin n) K) := map σ.toRingHom '' S

theorem coefficientVanishing_conjugate_iff (σ : K ≃+* K)
    (S : Set (MvPolynomial (Fin n) K)) (P : MvPolynomial (Fin n →₀ ℕ) K) :
    coefficientVanishing (conjugateSet σ S) (map σ.toRingHom P) ↔
      coefficientVanishing S P := by
  constructor
  · intro h F hF
    apply σ.injective
    rw [map_zero, ← eval_coeff_map]
    exact h _ ⟨F,hF,rfl⟩
  · intro h G hG
    obtain ⟨F,hF,rfl⟩ := hG
    rw [eval_coeff_map, h F hF, map_zero]

theorem map_matrix_inverse (σ : K ≃+* K) (B : Matrix (Fin n) (Fin n) K)
    (hB : Function.Injective B.mulVec) :
    (B.map σ.toRingHom)⁻¹ = B⁻¹.map σ.toRingHom := by
  apply Matrix.inv_eq_left_inv
  change σ.toRingHom.mapMatrix B⁻¹ * σ.toRingHom.mapMatrix B = 1
  rw [← map_mul, Matrix.nonsing_inv_mul B
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hB)), map_one]

theorem curve_map (σ : K ≃+* K) (F : MvPolynomial (Fin n) K)
    (w : Fin n → ℤ) (t : K) :
    map σ.toRingHom (curve F w t) = curve (map σ.toRingHom F) w (σ t) := by
  ext e
  simp only [coeff_map, coeff_curve, map_mul, map_pow]
  rfl

def originalCurve (F : MvPolynomial (Fin n) K) (f : WeightFrame K n) (t : K) :
    MvPolynomial (Fin n) K := restrict f.matrix⁻¹ (curve (restrict f.matrix F) f.weight t)

theorem originalCurve_map (σ : K ≃+* K) (F : MvPolynomial (Fin n) K)
    (f : WeightFrame K n) (t : K) :
    map σ.toRingHom (originalCurve F f t) =
      originalCurve (map σ.toRingHom F) (f.conjugate σ) (σ t) := by
  unfold originalCurve
  rw [map_restrict, curve_map, map_restrict]
  change restrict _ _ = restrict (f.matrix.map σ.toRingHom)⁻¹ _
  rw [map_matrix_inverse σ f.matrix f.injective]
  rfl

theorem curve_homogeneous (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (w : Fin n → ℤ) (t : K) : (curve F w t).IsHomogeneous d := by
  intro e he
  apply hF
  intro hz
  apply he
  rw [coeff_curve,hz,zero_mul]

@[simp] theorem originalCurve_one (F : MvPolynomial (Fin n) K) (f : WeightFrame K n) :
    originalCurve F f 1 = F := by
  unfold originalCurve
  rw [curve_one, restrict_restrict, Matrix.mul_nonsing_inv f.matrix
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp f.injective)),
    restrict_one]

/-- Away from zero this is the literal conjugated diagonal orbit curve.
The multiplication order follows the pullback action on polynomials. -/
theorem originalCurve_eq_restrict (F : MvPolynomial (Fin n) K)
    (f : WeightFrame K n)
    (hW : HasNonnegativeWeights (restrict f.matrix F) f.weight)
    (t : K) (ht : t ≠ 0) :
    originalCurve F f t = restrict
      (f.matrix * diagonalWeight f.weight t * f.matrix⁻¹) F := by
  unfold originalCurve
  rw [curve_eq_restrict _ _ hW t ht, restrict_restrict, restrict_restrict]
  rw [Matrix.mul_assoc]

theorem originalCurve_zero (F : MvPolynomial (Fin n) K)
    (f : WeightFrame K n)
    (hW : HasNonnegativeWeights (restrict f.matrix F) f.weight) :
    originalCurve F f 0 = restrict f.matrix⁻¹
      (zeroWeightPart (restrict f.matrix F) f.weight) := by
  unfold originalCurve
  rw [curve_zero _ _ hW]

/-- Polynomial pullback of a coefficient-space equation to the actual curve.
`d` is the degree of the representation, not a chosen degree of a test equation. -/
def originalTest (d : ℕ) (F : MvPolynomial (Fin n) K) (f : WeightFrame K n)
    (P : MvPolynomial (Fin n →₀ ℕ) K) : Polynomial K :=
  curveTest (restrict f.matrix F) f.weight
    (aeval (coefficientRestriction f.matrix⁻¹ d) P)

theorem originalTest_eval (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (f : WeightFrame K n) (P : MvPolynomial (Fin n →₀ ℕ) K) (t : K) :
    (originalTest d F f P).eval t = eval (fun e => coeff e (originalCurve F f t)) P := by
  rw [originalTest,eval_curveTest]
  change aeval (fun e => coeff e (curve (restrict f.matrix F) f.weight t))
    (aeval (coefficientRestriction f.matrix⁻¹ d) P) = _
  rw [MvPolynomial.comp_aeval_apply]
  have hc := funext (eval_coefficientRestriction f.matrix⁻¹
    (curve (restrict f.matrix F) f.weight t)
    (curve_homogeneous _ (homogeneous_restrict _ F hF) _ _))
  change (fun e => aeval (fun m => coeff m (curve (restrict f.matrix F) f.weight t))
    (coefficientRestriction f.matrix⁻¹ d e)) = _ at hc
  rw [hc]
  rfl

theorem originalTest_map [Infinite K] (σ : K ≃+* K)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (f : WeightFrame K n) (P : MvPolynomial (Fin n →₀ ℕ) K) :
    Polynomial.map σ.toRingHom (originalTest d F f P) =
      originalTest d (map σ.toRingHom F) (f.conjugate σ) (map σ.toRingHom P) := by
  apply Polynomial.funext
  intro t
  obtain ⟨t,rfl⟩ := σ.surjective t
  change Polynomial.eval (σ.toRingHom t) _ = _
  rw [Polynomial.eval_map_apply, originalTest_eval F hF,
    originalTest_eval _ (hF.map σ.toRingHom), ← originalCurve_map, eval_coeff_map]
  rfl

/-- Exponents occurring in some element of the pulled-back vanishing ideal.
Taking their minimum is precisely the order of that ideal at t=0. -/
def relativeOrderSupport (d : ℕ) (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (f : WeightFrame K n) : Set ℕ :=
  {m | ∃ P : MvPolynomial (Fin n →₀ ℕ) K,
    coefficientVanishing S P ∧ (originalTest d F f P).coeff m ≠ 0}

/-- The empty pullback ideal is assigned order zero.  For a closed target
avoiding F it is nonempty, as proved below, so this convention is immaterial. -/
def relativeOrder (d : ℕ) (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (f : WeightFrame K n) : ℕ :=
  sInf (relativeOrderSupport d F S f)

theorem relativeOrderSupport_map [Infinite K] (σ : K ≃+* K)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (f : WeightFrame K n) :
    relativeOrderSupport d (map σ.toRingHom F) (conjugateSet σ S) (f.conjugate σ) =
      relativeOrderSupport d F S f := by
  ext m
  constructor
  · rintro ⟨P,hP,hc⟩
    let Q := map σ.symm.toRingHom P
    have hPQ : map σ.toRingHom Q = P := map_map_symm σ P
    refine ⟨Q, ?_, ?_⟩
    · apply (coefficientVanishing_conjugate_iff σ S Q).mp
      rwa [hPQ]
    · intro hz
      apply hc
      rw [← hPQ, ← originalTest_map σ F hF, Polynomial.coeff_map, hz, map_zero]
  · rintro ⟨P,hP,hc⟩
    refine ⟨map σ.toRingHom P,
      (coefficientVanishing_conjugate_iff σ S P).mpr hP, ?_⟩
    rw [← originalTest_map σ F hF, Polynomial.coeff_map]
    exact fun hz => hc (σ.injective (hz.trans (map_zero σ.toRingHom).symm))

theorem relativeOrder_map [Infinite K] (σ : K ≃+* K)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (f : WeightFrame K n) :
    relativeOrder d (map σ.toRingHom F) (conjugateSet σ S) (f.conjugate σ) =
      relativeOrder d F S f := by
  unfold relativeOrder
  rw [relativeOrderSupport_map σ F hF]

theorem relativeOrderSupport_nonempty (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) (S : Set (MvPolynomial (Fin n) K))
    (hS : coefficientClosed S) (hnot : F ∉ S) (f : WeightFrame K n) :
    (relativeOrderSupport d F S f).Nonempty := by
  classical
  have hp : ∃ P, coefficientVanishing S P ∧ eval (fun e => coeff e F) P ≠ 0 := by
    by_contra h
    push_neg at h
    exact hnot (hS F h)
  obtain ⟨P,hP,hp⟩ := hp
  have ht : originalTest d F f P ≠ 0 := by
    intro hz
    have h := congrArg (fun Q : Polynomial K => Q.eval 1) hz
    dsimp only at h
    rw [originalTest_eval F hF, originalCurve_one, Polynomial.eval_zero] at h
    exact hp h
  obtain ⟨m,hm⟩ : ∃ m, (originalTest d F f P).coeff m ≠ 0 := by
    by_contra h
    push_neg at h
    exact ht (Polynomial.ext (by simpa only [Polynomial.coeff_zero] using h))
  exact ⟨m,P,hP,hm⟩

/-- Every pulled-back ideal equation is divisible by the exact common power
of t.  Thus the order definition is the ordinary ideal-adic order. -/
theorem relativeOrder_dvd (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (f : WeightFrame K n)
    (P : MvPolynomial (Fin n →₀ ℕ) K) (hP : coefficientVanishing S P) :
    Polynomial.X ^ relativeOrder d F S f ∣ originalTest d F f P := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro m hm
  by_contra hc
  exact Nat.notMem_of_lt_sInf hm ⟨P,hP,hc⟩

theorem relativeOrder_attained (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) (S : Set (MvPolynomial (Fin n) K))
    (hS : coefficientClosed S) (hnot : F ∉ S) (f : WeightFrame K n) :
    ∃ P, coefficientVanishing S P ∧
      (originalTest d F f P).coeff (relativeOrder d F S f) ≠ 0 :=
  Nat.sInf_mem (relativeOrderSupport_nonempty F hF S hS hnot f)

/-- Positive relative order is equivalent to actual specialization into the
closed target.  In admissible weights this is the genuine one-parameter limit. -/
theorem relativeOrder_pos_iff (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) (S : Set (MvPolynomial (Fin n) K))
    (hS : coefficientClosed S) (hnot : F ∉ S) (f : WeightFrame K n) :
    0 < relativeOrder d F S f ↔ originalCurve F f 0 ∈ S := by
  constructor
  · intro ho
    apply hS
    intro P hP
    have hz := Polynomial.X_pow_dvd_iff.mp (relativeOrder_dvd F S f P hP) 0 ho
    have he := originalTest_eval F hF f P 0
    rw [← Polynomial.coeff_zero_eq_eval_zero] at he
    exact he.symm.trans hz
  · intro hx
    by_contra hn
    have hz : relativeOrder d F S f = 0 := by omega
    obtain ⟨P,hP,hc⟩ := relativeOrder_attained F hF S hS hnot f
    apply hc
    rw [hz, Polynomial.coeff_zero_eq_eval_zero, originalTest_eval F hF]
    exact hP _ hx

end HessianTheorem11.ReducedRelative
