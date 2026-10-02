import TranslatedDepthSeven.QbarCoefficientExtension

/-!
# Primeness over every algebraic coefficient field from the Qbar test

For a rational polynomial ideal, primeness after literal coefficient
extension to `Qbar` implies primeness after coefficient extension to every
algebraic field extension of `ℚ`.  The proof embeds that field in `Qbar`,
uses transitivity of coefficient extension, and contracts the resulting
prime ideal along a faithfully flat polynomial-ring extension.

This is the complete algebraic part of the usual algebraic-closure
criterion for geometric integrality.  In particular, any remaining passage
to real coefficients concerns only the transcendental extension from the
relative algebraic closure of `ℚ` in `ℝ` to `ℝ`.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1000000

universe u v w

noncomputable local instance mvPolynomialCoefficientAlgebra
    {K : Type u} {L : Type v} {σ : Type w}
    [CommSemiring K] [CommSemiring L] [Algebra K L] :
    Algebra (MvPolynomial σ K) (MvPolynomial σ L) :=
  MvPolynomial.algebraMvPolynomial

/-- The polynomial coefficient extension `K[X] -> L[X]`, written as the
standard scalar-extension tensor product and regarded linearly over
`K[X]`. -/
private noncomputable def mvPolynomialTensorLinearEquiv
    {K : Type u} {L : Type v} {σ : Type w}
    [Field K] [Field L] [Algebra K L] :
    MvPolynomial σ L ≃ₗ[MvPolynomial σ K]
      ((MvPolynomial σ K) ⊗[K] L) := by
  let eAlg : ((MvPolynomial σ K) ⊗[K] L) ≃ₐ[K]
      MvPolynomial σ L :=
    (Algebra.TensorProduct.comm K (MvPolynomial σ K) L).trans
      ((MvPolynomial.algebraTensorAlgEquiv K L
        (σ := σ)).restrictScalars K)
  exact
    { eAlg.symm.toEquiv with
      map_add' := eAlg.symm.map_add
      map_smul' := by
        intro a b
        simp [eAlg, Algebra.smul_def]
        change (algebraMap (MvPolynomial σ K)
          ((MvPolynomial σ K) ⊗[K] L)) a *
            (Algebra.TensorProduct.comm K (MvPolynomial σ K) L).symm
              ((MvPolynomial.algebraTensorAlgEquiv K L
                (σ := σ)).symm b) = _
        exact (Algebra.smul_def a _).symm }

/-- Polynomial coefficient extension along an arbitrary field extension is
faithfully flat.  Kept as a theorem rather than a global instance to avoid
overlapping the concrete `ℚ -> ℝ` and `ℚ -> Qbar` instances. -/
theorem mvPolynomial_faithfullyFlat
    {K : Type u} {L : Type v} {σ : Type w}
    [Field K] [Field L] [Algebra K L] :
    Module.FaithfullyFlat (MvPolynomial σ K) (MvPolynomial σ L) := by
  letI : Module.FaithfullyFlat K L := inferInstance
  letI : Module.FaithfullyFlat (MvPolynomial σ K)
      ((MvPolynomial σ K) ⊗[K] L) := inferInstance
  exact Module.FaithfullyFlat.of_linearEquiv
    (MvPolynomial σ K) ((MvPolynomial σ K) ⊗[K] L)
      mvPolynomialTensorLinearEquiv

/-- A rational ideal passing the `Qbar` prime test remains prime after
coefficient extension to every algebraic field extension of `ℚ`. -/
theorem algebraicCoefficientExtension_isPrime_of_qbarExtension_isPrime
    {E : Type u} {σ : Type w}
    [Field E] [Algebra ℚ E] [Algebra.IsAlgebraic ℚ E]
    (I : Ideal (MvPolynomial σ ℚ))
    (hQbar :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime) :
    (I.map (MvPolynomial.map (algebraMap ℚ E))).IsPrime := by
  let ι : E →ₐ[ℚ] Qbar := IsAlgClosed.lift
  letI : Algebra E Qbar := ι.toRingHom.toAlgebra
  let f : MvPolynomial σ ℚ →+* MvPolynomial σ E :=
    MvPolynomial.map (algebraMap ℚ E)
  let g : MvPolynomial σ E →+* MvPolynomial σ Qbar :=
    MvPolynomial.map (algebraMap E Qbar)
  let h : MvPolynomial σ ℚ →+* MvPolynomial σ Qbar :=
    MvPolynomial.map (algebraMap ℚ Qbar)
  have hgf : g.comp f = h := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [f, g, h]
    · intro i
      simp [f, g, h]
  have hmap : (I.map f).map g = I.map h := by
    rw [Ideal.map_map, hgf]
  have hprimeMap : ((I.map f).map g).IsPrime := by
    rw [hmap]
    exact hQbar
  have hprimeComap : (((I.map f).map g).comap g).IsPrime :=
    hprimeMap.comap g
  letI : Module.FaithfullyFlat (MvPolynomial σ E)
      (MvPolynomial σ Qbar) := by
    exact mvPolynomial_faithfullyFlat
  have hcontract : ((I.map f).map g).comap g = I.map f := by
    change ((I.map f).map (algebraMap (MvPolynomial σ E)
      (MvPolynomial σ Qbar))).comap
        (algebraMap (MvPolynomial σ E) (MvPolynomial σ Qbar)) = I.map f
    exact Ideal.comap_map_eq_self_of_faithfullyFlat (I.map f)
  rw [hcontract] at hprimeComap
  exact hprimeComap

/-- In particular, the `Qbar` prime test already implies primeness of the
original rational ideal. -/
theorem isPrime_of_qbarCoefficientExtension_isPrime
    {σ : Type w} (I : Ideal (MvPolynomial σ ℚ))
    (hQbar :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime) :
    I.IsPrime := by
  have hp := algebraicCoefficientExtension_isPrime_of_qbarExtension_isPrime
    (E := ℚ) I hQbar
  have hcoeff : MvPolynomial.map (algebraMap ℚ ℚ) =
      RingHom.id (MvPolynomial σ ℚ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp
  rw [hcoeff, Ideal.map_id] at hp
  exact hp

/-- The exact real-algebraic intermediate coefficient field already has a
prime extended ideal.  Thus the unformalized real step, if needed, begins
only after adjoining transcendental real coefficients. -/
theorem realAlgebraicCoefficientExtension_isPrime_of_qbarExtension_isPrime
    {σ : Type w} (I : Ideal (MvPolynomial σ ℚ))
    (hQbar :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime) :
    (I.map (MvPolynomial.map (algebraMap ℚ
      (algebraicClosure ℚ ℝ)))).IsPrime := by
  exact algebraicCoefficientExtension_isPrime_of_qbarExtension_isPrime
    (E := algebraicClosure ℚ ℝ) I hQbar

end

end TranslatedDepthSeven
