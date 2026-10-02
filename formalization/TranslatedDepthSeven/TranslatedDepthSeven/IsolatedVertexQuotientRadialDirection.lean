import TranslatedDepthSeven.IsolatedVertexQuotientVertexCell
import TranslatedDepthSeven.LowRadialScale
import TranslatedDepthSeven.RankSevenDegreeOneHighLedger
import TranslatedDepthSeven.RankSevenDegreeOneProperStarSource
import TranslatedDepthSeven.PrimitiveDirectionNormalization

/-!
# Intrinsic directions of radial isolated-vertex quotient records

A radial quotient component is a projective degree-one curve through the
translated cone vertex `(m,-b)`.  Away from the unique affine point with
`b + m w = 0`, the second rational point `(1,w)` determines that line.
Consequently every other affine point `(1,z)` on the same component has
`b + m z` rationally proportional to `b + m w`.

The only outside input below is the ordinary degree-one-variety theorem,
stated in its literal two-point spanning form.  It contains no point count,
height estimate, residue statement, or assertion about the quotient family.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

namespace StandardAG

/-- An integral projective curve of degree one is the projective line
spanned by any two distinct projective points on it.  The first displayed
affine-cone representative is explicitly nonzero.  Together with the
absence of a scalar relating the second representative to the first, this
expresses linear independence without any additional projectivization API.
Without the nonzero condition, taking `x = 0` and `y ≠ 0` would satisfy
the scalar condition but would not span the two-dimensional line cone.
-/
def QbarIntegralProjectiveDegreeOneCurveTwoPointSpan : Prop :=
  ∀ (N : ℕ) (P : Ideal (MvPolynomial (Fin (N + 1)) Qbar)),
    P.IsPrime →
    P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) Qbar) →
    HasProjectiveDimensionDegree P 1 1 →
    ∀ (x y : Fin (N + 1) → Qbar),
      x ∈ affineIdealZeroLocus P →
      y ∈ affineIdealZeroLocus P →
      x ≠ 0 →
      (¬ ∃ a : Qbar, y = a • x) →
      ∀ z : Fin (N + 1) → Qbar,
        z ∈ affineIdealZeroLocus P →
        ∃ a c : Qbar, z = a • x + c • y

end StandardAG

/-- The integral base-cone direction attached to an affine quotient point. -/
def isolatedVertexQuotientBaseDirection
    (b w : IntVector 12) (m : ℤ) : IntVector 12 :=
  integralQuotientAffinePoint b w m

/-- A fixed nonzero lower-coordinate vector, used only to totalize the
projective base-direction map at its unique zero. -/
def isolatedVertexQuotientFirstLowerDirection : IntVector 12 :=
  fun i ↦ if i = 0 then 1 else 0

theorem isolatedVertexQuotientFirstLowerDirection_ne_zero :
    isolatedVertexQuotientFirstLowerDirection ≠ 0 := by
  intro h
  have hzero := congrFun h (0 : Fin 12)
  simp [isolatedVertexQuotientFirstLowerDirection] at hzero

/-- The rational projective class of `b + m w`, totalized at the unique
point where that vector vanishes.  Every use on the radial nonvertex cell
rewrites through the nonzero branch. -/
def isolatedVertexQuotientBaseProjectiveDirection
    (b : IntVector 12) (m : ℤ) (w : IntVector 12) :
    Projectivization ℚ (Fin 12 → ℚ) :=
  if hw : isolatedVertexQuotientBaseDirection b w m ≠ 0 then
    integralProjectiveClass
      (isolatedVertexQuotientBaseDirection b w m) hw
  else
    integralProjectiveClass isolatedVertexQuotientFirstLowerDirection
      isolatedVertexQuotientFirstLowerDirection_ne_zero

@[simp]
theorem isolatedVertexQuotientBaseProjectiveDirection_eq
    (b : IntVector 12) (m : ℤ) (w : IntVector 12)
    (hw : isolatedVertexQuotientBaseDirection b w m ≠ 0) :
    isolatedVertexQuotientBaseProjectiveDirection b m w =
      integralProjectiveClass
        (isolatedVertexQuotientBaseDirection b w m) hw := by
  simp [isolatedVertexQuotientBaseProjectiveDirection, hw]

/-- The affine map `w ↦ b + m w` is injective for nonzero integral `m`. -/
theorem isolatedVertexQuotientBaseDirection_injective
    (b : IntVector 12) {m : ℤ} (hm : m ≠ 0) :
    Function.Injective (fun w : IntVector 12 ↦
      isolatedVertexQuotientBaseDirection b w m) := by
  intro w z hwz
  funext i
  have hi := congrFun hwz i
  simp only [isolatedVertexQuotientBaseDirection,
    integralQuotientAffinePoint] at hi
  exact mul_left_cancel₀ hm (by linarith)

/-- In any finite quotient-point set, at most one point maps to the
translated cone origin `b + m w = 0`. -/
theorem card_filter_isolatedVertexQuotientBaseDirection_eq_zero_le_one
    (S : Finset (IntVector 12)) (b : IntVector 12) {m : ℤ} (hm : m ≠ 0) :
    (S.filter fun w ↦
      isolatedVertexQuotientBaseDirection b w m = 0).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro w hw z hz
  apply isolatedVertexQuotientBaseDirection_injective b hm
  exact (Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hz).2.symm

/-- Two nonvertex quotient points with the same projective base direction
lie on one rational affine line.  A primitive integral direction for that
line is obtained by normalizing the base direction of the first point; its
projective height is exactly the height of their common projective class.

This is purely rational linear algebra.  In particular it does not inspect
the quotient component containing either point. -/
theorem exists_primitiveDirection_of_baseProjectiveDirection_eq
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (w z : IntVector 12)
    (hw : isolatedVertexQuotientBaseDirection b w m ≠ 0)
    (hz : isolatedVertexQuotientBaseDirection b z m ≠ 0)
    (heq : isolatedVertexQuotientBaseProjectiveDirection b m z =
      isolatedVertexQuotientBaseProjectiveDirection b m w) :
    ∃ h : IntVector 12,
      PrimitiveDirection h ∧
      directionHeight h = primitiveRationalVectorHeight
        (isolatedVertexQuotientBaseProjectiveDirection b m w).rep ∧
      ∃ a : ℚ, ∀ i,
        ((z i - w i : ℤ) : ℚ) = a * (h i : ℚ) := by
  obtain ⟨h, t, hprimitive, ht, hscale, _hbound⟩ :=
    exists_bounded_primitiveDirection_of_ne_zero
      (isolatedVertexQuotientBaseDirection b w m) hw
  have hh : h ≠ 0 := by
    intro hzero
    obtain ⟨i, hi⟩ := hprimitive.exists_ne_zero
    exact hi (congrFun hzero i)
  have hclass : integralProjectiveClass h hh =
      isolatedVertexQuotientBaseProjectiveDirection b m w := by
    rw [isolatedVertexQuotientBaseProjectiveDirection_eq b m w hw]
    apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).2
    refine ⟨t, ?_⟩
    funext i
    simpa only [Pi.smul_apply, smul_eq_mul] using (hscale i).symm
  have hheight : directionHeight h = primitiveRationalVectorHeight
      (isolatedVertexQuotientBaseProjectiveDirection b m w).rep := by
    rw [← hclass,
      primitiveRationalVectorHeight_integralProjectiveClass_eq_directionHeight
        hprimitive hh]
  have heq' : integralProjectiveClass
        (isolatedVertexQuotientBaseDirection b z m) hz =
      integralProjectiveClass
        (isolatedVertexQuotientBaseDirection b w m) hw := by
    simpa only [isolatedVertexQuotientBaseProjectiveDirection_eq b m z hz,
      isolatedVertexQuotientBaseProjectiveDirection_eq b m w hw] using heq
  obtain ⟨r, _hr, hproportional⟩ :=
    exists_nonzero_rational_proportionality_of_integralProjectiveClass_eq
      (isolatedVertexQuotientBaseDirection b w m)
      (isolatedVertexQuotientBaseDirection b z m) hw hz heq'
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  refine ⟨h, hprimitive, hheight, (r - 1) / (t * (m : ℚ)), ?_⟩
  intro i
  have hri := hproportional i
  have hti := hscale i
  simp only [isolatedVertexQuotientBaseDirection,
    integralQuotientAffinePoint, Int.cast_add, Int.cast_mul] at hri hti
  push_cast at hri hti ⊢
  field_simp [ht, hmQ]
  rw [hti]
  linear_combination t * hri

/-- Set-valued form of
`exists_primitiveDirection_of_baseProjectiveDirection_eq`: one
normalization of the base direction of `w` parametrizes an entire finite
fibre of the projective base-direction map. -/
theorem exists_primitiveDirection_parametrizing_baseProjectiveFibre
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (S : Finset (IntVector 12)) (w : IntVector 12) (hwS : w ∈ S)
    (hnonzero : ∀ z ∈ S,
      isolatedVertexQuotientBaseDirection b z m ≠ 0)
    (hsame : ∀ z ∈ S,
      isolatedVertexQuotientBaseProjectiveDirection b m z =
        isolatedVertexQuotientBaseProjectiveDirection b m w) :
    ∃ h : IntVector 12,
      PrimitiveDirection h ∧
      directionHeight h = primitiveRationalVectorHeight
        (isolatedVertexQuotientBaseProjectiveDirection b m w).rep ∧
      ∀ z ∈ S, ∃ a : ℚ, ∀ i,
        ((z i - w i : ℤ) : ℚ) = a * (h i : ℚ) := by
  have hw := hnonzero w hwS
  obtain ⟨h, t, hprimitive, ht, hscale, _hbound⟩ :=
    exists_bounded_primitiveDirection_of_ne_zero
      (isolatedVertexQuotientBaseDirection b w m) hw
  have hh : h ≠ 0 := by
    intro hzero
    obtain ⟨i, hi⟩ := hprimitive.exists_ne_zero
    exact hi (congrFun hzero i)
  have hclass : integralProjectiveClass h hh =
      isolatedVertexQuotientBaseProjectiveDirection b m w := by
    rw [isolatedVertexQuotientBaseProjectiveDirection_eq b m w hw]
    apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).2
    refine ⟨t, ?_⟩
    funext i
    simpa only [Pi.smul_apply, smul_eq_mul] using (hscale i).symm
  have hheight : directionHeight h = primitiveRationalVectorHeight
      (isolatedVertexQuotientBaseProjectiveDirection b m w).rep := by
    rw [← hclass,
      primitiveRationalVectorHeight_integralProjectiveClass_eq_directionHeight
        hprimitive hh]
  refine ⟨h, hprimitive, hheight, ?_⟩
  intro z hzS
  have hz := hnonzero z hzS
  have heq : integralProjectiveClass
        (isolatedVertexQuotientBaseDirection b z m) hz =
      integralProjectiveClass
        (isolatedVertexQuotientBaseDirection b w m) hw := by
    simpa only [isolatedVertexQuotientBaseProjectiveDirection_eq b m z hz,
      isolatedVertexQuotientBaseProjectiveDirection_eq b m w hw] using
        hsame z hzS
  obtain ⟨r, _hr, hproportional⟩ :=
    exists_nonzero_rational_proportionality_of_integralProjectiveClass_eq
      (isolatedVertexQuotientBaseDirection b w m)
      (isolatedVertexQuotientBaseDirection b z m) hw hz heq
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  refine ⟨(r - 1) / (t * (m : ℚ)), ?_⟩
  intro i
  have hri := hproportional i
  have hti := hscale i
  simp only [isolatedVertexQuotientBaseDirection,
    integralQuotientAffinePoint, Int.cast_add, Int.cast_mul] at hri hti
  push_cast at hri hti ⊢
  field_simp [ht, hmQ]
  rw [hti]
  linear_combination t * hri

/-- If `(1,w)` is a nonvertex point of a radial degree-one component, then
every normalized affine point of that component has a base direction
rationally proportional to `b + m w`.

The scalar is first produced over `Qbar` by the degree-one linear-span
theorem.  Since both direction vectors are integral and the reference
direction is nonzero, one nonzero coordinate shows that scalar is rational.
-/
theorem exists_rational_proportional_baseDirection_of_radialComponent
    (hline : StandardAG.QbarIntegralProjectiveDegreeOneCurveTwoPointSpan)
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (P : Ideal (MvPolynomial (Fin 13) Qbar)) (s e : ℕ)
    (hradial : IsRadialQuotientNodeLine
      (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ)) P s e)
    (w : IntVector 12)
    (hw : geometricQuotientRationalHomogeneousAffinePoint w ∈
      affineIdealZeroLocus P)
    (hbase : isolatedVertexQuotientBaseDirection b w m ≠ 0)
    (z : IntVector 12)
    (hz : geometricQuotientRationalHomogeneousAffinePoint z ∈
      affineIdealZeroLocus P) :
    ∃ r : ℚ, ∀ i,
      (isolatedVertexQuotientBaseDirection b z m i : ℚ) =
        r * (isolatedVertexQuotientBaseDirection b w m i : ℚ) := by
  let vertex : Fin 13 → Qbar :=
    isolatedVertexQuotientProjectiveVertexVector
      (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ))
  let point : Fin 13 → Qbar :=
    geometricQuotientRationalHomogeneousAffinePoint w
  have hPdegree : HasProjectiveDimensionDegree P 1 1 := by
    simpa only [HasGeometricProjectiveDimensionDegree,
      hradial.2.2.1, hradial.2.2.2.1] using hradial.2.1
  have hnotScalar : ¬ ∃ a : Qbar, point = a • vertex := by
    rintro ⟨a, ha⟩
    have hfirst := congrFun ha 0
    have hfirst' : (1 : Qbar) = a * algebraMap ℚ Qbar (m : ℚ) := by
      simpa [point, vertex, geometricQuotientRationalHomogeneousAffinePoint,
        quotientRationalHomogeneousAffinePoint] using hfirst
    apply hbase
    funext i
    have hi := congrFun ha i.succ
    have hi' : algebraMap ℚ Qbar (w i : ℚ) =
        a * (-algebraMap ℚ Qbar (b i : ℚ)) := by
      simpa [point, vertex, geometricQuotientRationalHomogeneousAffinePoint,
        quotientRationalHomogeneousAffinePoint, qbarIntVector] using hi
    have hzeroQ : algebraMap ℚ Qbar
        (isolatedVertexQuotientBaseDirection b w m i : ℚ) = 0 := by
      simp only [isolatedVertexQuotientBaseDirection,
        integralQuotientAffinePoint, Int.cast_add, Int.cast_mul]
      rw [map_add, map_mul]
      change algebraMap ℚ Qbar (b i : ℚ) +
        algebraMap ℚ Qbar (m : ℚ) *
          algebraMap ℚ Qbar (w i : ℚ) = 0
      rw [hi']
      calc
        algebraMap ℚ Qbar (b i : ℚ) +
            algebraMap ℚ Qbar (m : ℚ) *
              (a * -algebraMap ℚ Qbar (b i : ℚ)) =
            (1 - a * algebraMap ℚ Qbar (m : ℚ)) *
              algebraMap ℚ Qbar (b i : ℚ) := by ring
        _ = 0 := by rw [← hfirst']; ring
    have hzeroRat :
        (isolatedVertexQuotientBaseDirection b w m i : ℚ) = 0 :=
      (map_eq_zero_iff (algebraMap ℚ Qbar)
        (FaithfulSMul.algebraMap_injective ℚ Qbar)).mp hzeroQ
    exact_mod_cast hzeroRat
  have hvertex_ne : vertex ≠ 0 := by
    intro hzero
    have hmbar : algebraMap ℚ Qbar (m : ℚ) = 0 := by
      simpa [vertex, isolatedVertexQuotientProjectiveVertexVector] using
        congrFun hzero 0
    have hmQ : (m : ℚ) = 0 :=
      (map_eq_zero_iff (algebraMap ℚ Qbar)
        (FaithfulSMul.algebraMap_injective ℚ Qbar)).mp hmbar
    exact hm (by exact_mod_cast hmQ)
  obtain ⟨a, c, hspan⟩ := hline 12 P hradial.1.1 hradial.1.2
    hPdegree vertex point hradial.2.2.2.2 hw hvertex_ne hnotScalar
    (geometricQuotientRationalHomogeneousAffinePoint z) hz
  have hfirst := congrFun hspan 0
  have hfirst' : (1 : Qbar) =
      a * algebraMap ℚ Qbar (m : ℚ) + c := by
    simpa [vertex, point, geometricQuotientRationalHomogeneousAffinePoint,
      quotientRationalHomogeneousAffinePoint] using hfirst
  have hQbar : ∀ i, algebraMap ℚ Qbar
      (isolatedVertexQuotientBaseDirection b z m i : ℚ) =
        c * algebraMap ℚ Qbar
          (isolatedVertexQuotientBaseDirection b w m i : ℚ) := by
    intro i
    have hi := congrFun hspan i.succ
    simp only [isolatedVertexQuotientBaseDirection,
      integralQuotientAffinePoint, Int.cast_add, Int.cast_mul]
    rw [map_add, map_mul, map_add, map_mul]
    change algebraMap ℚ Qbar (b i : ℚ) +
        algebraMap ℚ Qbar (m : ℚ) *
          algebraMap ℚ Qbar (z i : ℚ) =
      c * (algebraMap ℚ Qbar (b i : ℚ) +
        algebraMap ℚ Qbar (m : ℚ) *
          algebraMap ℚ Qbar (w i : ℚ))
    have hi' : algebraMap ℚ Qbar (z i : ℚ) =
        a * (-algebraMap ℚ Qbar (b i : ℚ)) +
          c * algebraMap ℚ Qbar (w i : ℚ) := by
      simpa [vertex, point, geometricQuotientRationalHomogeneousAffinePoint,
        quotientRationalHomogeneousAffinePoint, qbarIntVector] using hi
    have hone : 1 - a * algebraMap ℚ Qbar (m : ℚ) = c := by
      calc
        1 - a * algebraMap ℚ Qbar (m : ℚ) =
            (a * algebraMap ℚ Qbar (m : ℚ) + c) -
              a * algebraMap ℚ Qbar (m : ℚ) := by rw [← hfirst']
        _ = c := by ring
    rw [hi']
    calc
      algebraMap ℚ Qbar (b i : ℚ) +
          algebraMap ℚ Qbar (m : ℚ) *
            (a * -algebraMap ℚ Qbar (b i : ℚ) +
              c * algebraMap ℚ Qbar (w i : ℚ)) =
          (1 - a * algebraMap ℚ Qbar (m : ℚ)) *
              algebraMap ℚ Qbar (b i : ℚ) +
            c * algebraMap ℚ Qbar (m : ℚ) *
              algebraMap ℚ Qbar (w i : ℚ) := by ring
      _ = c * (algebraMap ℚ Qbar (b i : ℚ) +
          algebraMap ℚ Qbar (m : ℚ) *
            algebraMap ℚ Qbar (w i : ℚ)) := by
        rw [hone]
        ring
  obtain ⟨j, hj⟩ : ∃ j,
      isolatedVertexQuotientBaseDirection b w m j ≠ 0 := by
    by_contra hnone
    apply hbase
    funext j
    by_contra hj
    exact hnone ⟨j, hj⟩
  let r : ℚ :=
    (isolatedVertexQuotientBaseDirection b z m j : ℚ) /
      (isolatedVertexQuotientBaseDirection b w m j : ℚ)
  have hc : c = algebraMap ℚ Qbar r := by
    have hjQ := hQbar j
    have hden : algebraMap ℚ Qbar
        (isolatedVertexQuotientBaseDirection b w m j : ℚ) ≠ 0 := by
      intro hzero
      have hrat := (map_eq_zero_iff (algebraMap ℚ Qbar)
        (FaithfulSMul.algebraMap_injective ℚ Qbar)).mp hzero
      have hratne :
          (isolatedVertexQuotientBaseDirection b w m j : ℚ) ≠ 0 := by
        exact_mod_cast hj
      exact hratne hrat
    calc
      c = algebraMap ℚ Qbar
          (isolatedVertexQuotientBaseDirection b z m j : ℚ) /
            algebraMap ℚ Qbar
              (isolatedVertexQuotientBaseDirection b w m j : ℚ) :=
        (eq_div_iff hden).2 hjQ.symm
      _ = algebraMap ℚ Qbar r := by
        simp only [r, map_div₀]
  refine ⟨r, ?_⟩
  intro i
  have hiQ := hQbar i
  rw [hc] at hiQ
  rw [← map_mul] at hiQ
  exact (FaithfulSMul.algebraMap_injective ℚ Qbar) hiQ

/-- A nonvertex rational point on a radial component selects a primitive
integral direction for the whole affine part of that component.  The
normalization does not increase any coordinate of `b + m w`, and every
other integral affine point differs from `w` by a rational multiple of the
same primitive direction. -/
theorem exists_bounded_primitiveDirection_parametrizing_radialComponent
    (hline : StandardAG.QbarIntegralProjectiveDegreeOneCurveTwoPointSpan)
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (P : Ideal (MvPolynomial (Fin 13) Qbar)) (s e : ℕ)
    (hradial : IsRadialQuotientNodeLine
      (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ)) P s e)
    (w : IntVector 12)
    (hw : geometricQuotientRationalHomogeneousAffinePoint w ∈
      affineIdealZeroLocus P)
    (hbase : isolatedVertexQuotientBaseDirection b w m ≠ 0) :
    ∃ h : IntVector 12,
      PrimitiveDirection h ∧
      (∀ i, (h i).natAbs ≤
        (isolatedVertexQuotientBaseDirection b w m i).natAbs) ∧
      ∀ z : IntVector 12,
        geometricQuotientRationalHomogeneousAffinePoint z ∈
          affineIdealZeroLocus P →
        ∃ a : ℚ, ∀ i,
          ((z i - w i : ℤ) : ℚ) = a * (h i : ℚ) := by
  obtain ⟨h, t, hprimitive, ht, hscale, hbound⟩ :=
    exists_bounded_primitiveDirection_of_ne_zero
      (isolatedVertexQuotientBaseDirection b w m) hbase
  refine ⟨h, hprimitive, hbound, ?_⟩
  intro z hz
  obtain ⟨r, hr⟩ :=
    exists_rational_proportional_baseDirection_of_radialComponent
      hline b m hm P s e hradial w hw hbase z hz
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  refine ⟨(r - 1) / (t * (m : ℚ)), ?_⟩
  intro i
  have hri := hr i
  have hti := hscale i
  simp only [isolatedVertexQuotientBaseDirection,
    integralQuotientAffinePoint, Int.cast_add, Int.cast_mul] at hri hti
  push_cast at hri hti ⊢
  field_simp [ht, hmQ]
  rw [hti]
  linear_combination t * hri

end

end TranslatedDepthSeven
