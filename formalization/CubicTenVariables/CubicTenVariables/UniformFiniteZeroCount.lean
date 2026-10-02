import TranslatedDepthSeven.FixedConeResidueCount
import TranslatedDepthSeven.FiniteAlgebraPointCount

/-!
# Actual finite-field common zeros from finite quotient fibers

This module passes from literal equations to the corresponding quotient
algebra and sums actual projection fibers. It neither replaces the equations
by their radical nor assumes a point-count theorem.
-/

noncomputable section
namespace CubicTenVariables.UniformFiniteZeroCount
open MvPolynomial TranslatedDepthSeven
open scoped BigOperators

variable {K ι : Type*} [Field K] {n s : ℕ}

/-- The ideal of the displayed equation family, without radicalization. -/
def equationIdeal (f : ι → MvPolynomial (Fin n) K) : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (Set.range f)

/-- Every literal common zero of the original equations. -/
abbrev CommonZeros (f : ι → MvPolynomial (Fin n) K) :=
  {x : Fin n → K // ∀ i, eval x (f i) = 0}

theorem mem_zeroLocus_equationIdeal_iff (f : ι → MvPolynomial (Fin n) K)
    (x : Fin n → K) :
    x ∈ affineIdealZeroLocusOver (R := K) (K := K) (equationIdeal f) ↔
      ∀ i, eval x (f i) = 0 := by
  constructor
  · intro hx i
    simpa only [aeval_eq_eval] using hx (f i) (Ideal.subset_span ⟨i, rfl⟩)
  · intro hx
    have hker : equationIdeal f ≤ RingHom.ker (aeval x).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        aeval_eq_eval] using hx i
    exact fun g hg => hker hg

/-- Literal common zeros are exactly K-points of the original quotient. -/
def commonZerosEquivQuotientHom (f : ι → MvPolynomial (Fin n) K) :
    CommonZeros f ≃ ((MvPolynomial (Fin n) K ⧸ equationIdeal f) →ₐ[K] K) :=
  (Equiv.subtypeEquivRight (fun x => (mem_zeroLocus_equationIdeal_iff f x).symm)).trans
    (affineIdealZeroLocusEquivQuotientAlgHomOver (R := K) (K := K) (equationIdeal f))

section Field

/-- Finite-dimensional quotient algebras bound every actual common zero. -/
theorem natCard_commonZeros_le_finrank [Finite K]
    (f : ι → MvPolynomial (Fin n) K)
    [Module.Finite K (MvPolynomial (Fin n) K ⧸ equationIdeal f)] :
    Nat.card (CommonZeros f) ≤
      Module.finrank K (MvPolynomial (Fin n) K ⧸ equationIdeal f) := by
  rw [Nat.card_congr (commonZerosEquivQuotientHom f)]
  exact natCard_algHom_self_le_finrank K _

end Field

/-- Fixing the displayed polynomial parameters adds precisely L_j-t_j. -/
def fiberEquations (f : ι → MvPolynomial (Fin n) K)
    (L : Fin s → MvPolynomial (Fin n) K) (t : Fin s → K) :
    ι ⊕ Fin s → MvPolynomial (Fin n) K := Sum.elim f (fun j => L j - C (t j))

def fiberIdeal (f : ι → MvPolynomial (Fin n) K)
    (L : Fin s → MvPolynomial (Fin n) K) (t : Fin s → K) :
    Ideal (MvPolynomial (Fin n) K) := equationIdeal (fiberEquations f L t)

theorem fiberIdeal_eq_span_union (f : ι → MvPolynomial (Fin n) K)
    (L : Fin s → MvPolynomial (Fin n) K) (t : Fin s → K) :
    fiberIdeal f L t = Ideal.span (Set.range f ∪ Set.range (fun j => L j - C (t j))) := by
  unfold fiberIdeal equationIdeal
  congr 1
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨i, rfl⟩
    | inr j => exact Or.inr ⟨j, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr j, rfl⟩

theorem fiberEquations_zero_iff (f : ι → MvPolynomial (Fin n) K)
    (L : Fin s → MvPolynomial (Fin n) K) (t : Fin s → K) (x : Fin n → K) :
    (∀ i, eval x (fiberEquations f L t i) = 0) ↔
      (∀ i, eval x (f i) = 0) ∧ (∀ j, eval x (L j) = t j) := by
  constructor
  · intro h
    refine ⟨fun i => h (Sum.inl i), fun j => ?_⟩
    simpa [fiberEquations, sub_eq_zero] using h (Sum.inr j)
  · rintro ⟨hf, hL⟩ i
    cases i with
    | inl i => exact hf i
    | inr j => simp [fiberEquations, hL j]

/-- Every fiber of actual parameter evaluation is equivalent to the actual
common zeros of the augmented equations. -/
def projectionFiberEquiv (f : ι → MvPolynomial (Fin n) K)
    (L : Fin s → MvPolynomial (Fin n) K) (t : Fin s → K) :
    {x : CommonZeros f // (fun j => eval x.val (L j)) = t} ≃
      CommonZeros (fiberEquations f L t) where
  toFun x := ⟨x.val.val, (fiberEquations_zero_iff f L t x.val.val).mpr
    ⟨x.val.property, congrFun x.property⟩⟩
  invFun x := ⟨⟨x.val, ((fiberEquations_zero_iff f L t x.val).mp x.property).1⟩,
    funext ((fiberEquations_zero_iff f L t x.val).mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Uniform actual fiber counts sum over precisely (#K)^s parameter values. -/
theorem natCard_commonZeros_le_mul_pow_of_fibers [Finite K]
    (f : ι → MvPolynomial (Fin n) K)
    (L : Fin s → MvPolynomial (Fin n) K) (B : ℕ)
    (hB : ∀ t : Fin s → K, Nat.card (CommonZeros (fiberEquations f L t)) ≤ B) :
    Nat.card (CommonZeros f) ≤ B * (Nat.card K)^s := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (CommonZeros f) := Fintype.ofFinite _
  let projection : CommonZeros f → (Fin s → K) := fun x j => eval x.val (L j)
  have hfiber : ∀ t : Fin s → K,
      Nat.card {x : CommonZeros f // projection x = t} ≤ B := by
    intro t
    rw [Nat.card_congr (projectionFiberEquiv f L t)]
    exact hB t
  calc
    Nat.card (CommonZeros f) =
        ∑ t : Fin s → K, Nat.card {x : CommonZeros f // projection x = t} := by
      simpa only [Finset.card_univ, Nat.card_eq_fintype_card, Fintype.card_subtype] using
        (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (CommonZeros f)))
        (t := (Finset.univ : Finset (Fin s → K)))
        (f := projection) (by simp))
    _ ≤ ∑ _t : Fin s → K, B := Finset.sum_le_sum fun t _ => hfiber t
    _ = B * (Nat.card K)^s := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

/-- Finite quotient fibers with a uniform dimension bound give a bound for
all common zeros of the original equations, uniformly over every parameter. -/
theorem natCard_commonZeros_le_mul_pow [Finite K]
    (f : ι → MvPolynomial (Fin n) K)
    (L : Fin s → MvPolynomial (Fin n) K) (B : ℕ)
    (hfinite : ∀ t : Fin s → K,
      Module.Finite K (MvPolynomial (Fin n) K ⧸ fiberIdeal f L t))
    (hdim : ∀ t : Fin s → K,
      Module.finrank K (MvPolynomial (Fin n) K ⧸ fiberIdeal f L t) ≤ B) :
    Nat.card (CommonZeros f) ≤ B * (Nat.card K)^s := by
  apply natCard_commonZeros_le_mul_pow_of_fibers f L B
  intro t
  letI : Module.Finite K (MvPolynomial (Fin n) K ⧸ equationIdeal (fiberEquations f L t)) :=
    hfinite t
  exact (natCard_commonZeros_le_finrank (fiberEquations f L t)).trans (hdim t)

end CubicTenVariables.UniformFiniteZeroCount
