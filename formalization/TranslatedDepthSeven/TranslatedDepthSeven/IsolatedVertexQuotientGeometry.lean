import TranslatedDepthSeven.ProjectiveConeHilbertShift
import TranslatedDepthSeven.IsolatedVertexStrictInputBridge
import TranslatedDepthSeven.IsolatedVertexQuotientTangentPacket
import Mathlib.Algebra.CharZero.Infinite

/-!
# Projective geometry of the isolated-vertex quotient

This file connects the literal integral equation reduction in
`IsolatedVertexStrictInputBridge` to the rational homogeneous ideal of the
quotient fourfold.  The equation and quotient-ring identities are proved in
the kernel.  The two remaining projective-geometric implications are stated
as narrow textbook propositions: projective cone descent for dimension,
degree and geometric integrality, and the elementary correspondence between
vertices of a cone and vertices of its base.  Neither proposition contains a
point-counting assertion.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace IntegralUnimodularChange

/-- The same integral unimodular substitution after scalar extension to
`ℚ`. -/
def rationalPolynomialEquiv {m : ℕ} (U : IntegralUnimodularChange m) :
    MvPolynomial (Fin m) ℚ ≃ₐ[ℚ] MvPolynomial (Fin m) ℚ :=
  AlgEquiv.ofAlgHom
    (polynomialMatrixSubstitution
      (U.inverse.map (Int.castRingHom ℚ)))
    (polynomialMatrixSubstitution
      (U.forward.map (Int.castRingHom ℚ)))
    (by
      rw [polynomialMatrixSubstitution_comp, ← Matrix.map_mul,
        U.forward_mul_inverse]
      apply MvPolynomial.algHom_ext
      intro i
      classical
      simp [polynomialMatrixSubstitution, matrixLinearPolynomial,
        Matrix.one_apply])
    (by
      rw [polynomialMatrixSubstitution_comp, ← Matrix.map_mul,
        U.inverse_mul_forward]
      apply MvPolynomial.algHom_ext
      intro i
      classical
      simp [polynomialMatrixSubstitution, matrixLinearPolynomial,
        Matrix.one_apply])

/-- Rationalization commutes exactly with the displayed unimodular
substitution. -/
theorem map_intCast_polynomialEquiv {m : ℕ}
    (U : IntegralUnimodularChange m)
    (f : MvPolynomial (Fin m) ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ) (U.polynomialEquiv f) =
      U.rationalPolynomialEquiv
        (MvPolynomial.map (Int.castRingHom ℚ) f) := by
  let lhs : MvPolynomial (Fin m) ℤ →+* MvPolynomial (Fin m) ℚ :=
    (MvPolynomial.map (Int.castRingHom ℚ)).comp
      U.polynomialEquiv.toRingEquiv.toRingHom
  let rhs : MvPolynomial (Fin m) ℤ →+* MvPolynomial (Fin m) ℚ :=
    U.rationalPolynomialEquiv.toRingEquiv.toRingHom.comp
      (MvPolynomial.map (Int.castRingHom ℚ))
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, rhs, rationalPolynomialEquiv, polynomialEquiv,
        polynomialMatrixSubstitution]
    · intro i
      simp [lhs, rhs, rationalPolynomialEquiv, polynomialEquiv,
        polynomialMatrixSubstitution, matrixLinearPolynomial]
  change lhs f = rhs f
  exact RingHom.congr_fun hhom f

/-- The same integral matrix substitution over an arbitrary coefficient
field containing `ℚ`. -/
def coefficientFieldPolynomialEquiv {m : ℕ}
    (U : IntegralUnimodularChange m)
    (E : Type*) [Field E] [Algebra ℚ E] :
    MvPolynomial (Fin m) E ≃ₐ[E] MvPolynomial (Fin m) E :=
  letI : Infinite E := Infinite.of_injective
    (algebraMap ℚ E) (RingHom.injective (algebraMap ℚ E))
  AlgEquiv.ofAlgHom
    (polynomialMatrixSubstitution
      (U.inverse.map (Int.castRingHom E)))
    (polynomialMatrixSubstitution
      (U.forward.map (Int.castRingHom E)))
    (by
      rw [polynomialMatrixSubstitution_comp, ← Matrix.map_mul,
        U.forward_mul_inverse]
      apply MvPolynomial.algHom_ext
      intro i
      classical
      simp [polynomialMatrixSubstitution, matrixLinearPolynomial,
        Matrix.one_apply])
    (by
      rw [polynomialMatrixSubstitution_comp, ← Matrix.map_mul,
        U.inverse_mul_forward]
      apply MvPolynomial.algHom_ext
      intro i
      classical
      simp [polynomialMatrixSubstitution, matrixLinearPolynomial,
        Matrix.one_apply])

/-- Coefficient extension commutes with the unimodular linear
substitution. -/
theorem map_rationalPolynomialEquiv {m : ℕ}
    (U : IntegralUnimodularChange m)
    (E : Type*) [Field E] [Algebra ℚ E]
    (f : MvPolynomial (Fin m) ℚ) :
    MvPolynomial.map (algebraMap ℚ E) (U.rationalPolynomialEquiv f) =
      U.coefficientFieldPolynomialEquiv E
        (MvPolynomial.map (algebraMap ℚ E) f) := by
  let lhs : MvPolynomial (Fin m) ℚ →+* MvPolynomial (Fin m) E :=
    (MvPolynomial.map (algebraMap ℚ E)).comp
      U.rationalPolynomialEquiv.toRingEquiv.toRingHom
  let rhs : MvPolynomial (Fin m) ℚ →+* MvPolynomial (Fin m) E :=
    (U.coefficientFieldPolynomialEquiv E).toRingEquiv.toRingHom.comp
      (MvPolynomial.map (algebraMap ℚ E))
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, rhs, rationalPolynomialEquiv,
        coefficientFieldPolynomialEquiv, polynomialMatrixSubstitution]
    · intro i
      simp [lhs, rhs, rationalPolynomialEquiv,
        coefficientFieldPolynomialEquiv, polynomialMatrixSubstitution,
        matrixLinearPolynomial]
  change lhs f = rhs f
  exact RingHom.congr_fun hhom f

/-- Ideal extension commutes with the same substitution. -/
theorem map_map_rationalPolynomialEquiv {m : ℕ}
    (U : IntegralUnimodularChange m)
    (E : Type*) [Field E] [Algebra ℚ E]
    (I : Ideal (MvPolynomial (Fin m) ℚ)) :
    (I.map U.rationalPolynomialEquiv).map
        (MvPolynomial.map (algebraMap ℚ E)) =
      (I.map (MvPolynomial.map (algebraMap ℚ E))).map
        (U.coefficientFieldPolynomialEquiv E) := by
  change Ideal.map (MvPolynomial.map (algebraMap ℚ E))
      (Ideal.map U.rationalPolynomialEquiv.toRingEquiv.toRingHom I) =
    Ideal.map (U.coefficientFieldPolynomialEquiv E).toRingEquiv.toRingHom
      (Ideal.map (MvPolynomial.map (algebraMap ℚ E)) I)
  rw [Ideal.map_map, Ideal.map_map]
  apply congrArg (fun φ : MvPolynomial (Fin m) ℚ →+*
      MvPolynomial (Fin m) E ↦ I.map φ)
  apply MvPolynomial.ringHom_ext
  · intro a
    exact U.map_rationalPolynomialEquiv E (MvPolynomial.C a)
  · intro i
    exact map_rationalPolynomialEquiv U E (MvPolynomial.X i)

end IntegralUnimodularChange

/-- Geometric primeness is invariant under the rational unimodular
coordinate substitution. -/
theorem geometricallyPrime_map_rationalPolynomialEquiv_iff {m : ℕ}
    (U : IntegralUnimodularChange m)
    (I : Ideal (MvPolynomial (Fin m) ℚ)) :
    GeometricallyPrimeMvPolynomialIdeal
        (I.map U.rationalPolynomialEquiv) ↔
      GeometricallyPrimeMvPolynomialIdeal I := by
  constructor
  · intro h E _ _
    let φ := U.coefficientFieldPolynomialEquiv E
    have hbase :
        ((I.map U.rationalPolynomialEquiv).map
          (MvPolynomial.map (algebraMap ℚ E))) =
          (I.map (MvPolynomial.map (algebraMap ℚ E))).map φ := by
      simpa [φ] using U.map_map_rationalPolynomialEquiv E I
    have hprime :
        ((I.map (MvPolynomial.map (algebraMap ℚ E))).map φ).IsPrime := by
      rw [← hbase]
      exact h E
    letI : ((I.map (MvPolynomial.map
      (algebraMap ℚ E))).map φ).IsPrime := hprime
    have hback :
        (((I.map (MvPolynomial.map
          (algebraMap ℚ E))).map φ).map φ.symm).IsPrime :=
      Ideal.map_isPrime_of_equiv φ.symm
    have hundo :
        ((I.map (MvPolynomial.map
          (algebraMap ℚ E))).map φ).map φ.symm =
            I.map (MvPolynomial.map (algebraMap ℚ E)) := by
      exact Ideal.map_of_equiv φ.toRingEquiv
    rw [hundo] at hback
    exact hback
  · intro h E _ _
    let φ := U.coefficientFieldPolynomialEquiv E
    have hbase :
        ((I.map U.rationalPolynomialEquiv).map
          (MvPolynomial.map (algebraMap ℚ E))) =
          (I.map (MvPolynomial.map (algebraMap ℚ E))).map φ := by
      simpa [φ] using U.map_map_rationalPolynomialEquiv E I
    rw [hbase]
    letI : (I.map (MvPolynomial.map
      (algebraMap ℚ E))).IsPrime := h E
    exact Ideal.map_isPrime_of_equiv φ

/-- Rationalization of a finite equation family commutes with the
unimodular substitution. -/
theorem rationalizedEquationFinset_transformEquationFinset
    {m : ℕ} (U : IntegralUnimodularChange m)
    (equations : Finset (MvPolynomial (Fin m) ℤ)) :
    rationalizedEquationFinset (U.transformEquationFinset equations) =
      (rationalizedEquationFinset equations).map
        U.rationalPolynomialEquiv.toEquiv.toEmbedding := by
  classical
  ext f
  simp only [rationalizedEquationFinset,
    IntegralUnimodularChange.transformEquationFinset,
    Finset.mem_image, Finset.mem_map]
  constructor
  · rintro ⟨g, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) h, ⟨h, hh, rfl⟩, ?_⟩
    exact (IntegralUnimodularChange.map_intCast_polynomialEquiv U h).symm
  · rintro ⟨g, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨U.polynomialEquiv h, ⟨h, hh, rfl⟩, ?_⟩
    exact IntegralUnimodularChange.map_intCast_polynomialEquiv U h

/-- The rational ideal generated by rationalizing a finite integral family
is the scalar extension of its integral span. -/
theorem finiteEquationIdeal_rationalized_eq_map_span
    {m : ℕ} (equations : Finset (MvPolynomial (Fin m) ℤ)) :
    finiteEquationIdeal (rationalizedEquationFinset equations) =
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
        (Ideal.span (equations : Set (MvPolynomial (Fin m) ℤ))) := by
  rw [finiteEquationIdeal, rationalizedEquationFinset, Ideal.map_span]
  apply congrArg Ideal.span
  ext f
  simp

/-- At ideal level, rationalized unimodular substitution is literal ideal
transport by the rational polynomial automorphism. -/
theorem finiteEquationIdeal_transform_rationalized
    {m : ℕ} (U : IntegralUnimodularChange m)
    (equations : Finset (MvPolynomial (Fin m) ℤ)) :
    finiteEquationIdeal
        (rationalizedEquationFinset (U.transformEquationFinset equations)) =
      (finiteEquationIdeal (rationalizedEquationFinset equations)).map
        U.rationalPolynomialEquiv := by
  rw [rationalizedEquationFinset_transformEquationFinset]
  unfold finiteEquationIdeal
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  exact Finset.coe_map U.rationalPolynomialEquiv.toEquiv.toEmbedding
    (rationalizedEquationFinset equations)

/-- Rationalization also commutes exactly with adjoining an unused first
coordinate. -/
theorem rationalizedEquationFinset_liftEquationFinsetAfterFirst
    {n : ℕ} (equations : Finset (MvPolynomial (Fin n) ℤ)) :
    rationalizedEquationFinset (liftEquationFinsetAfterFirst equations) =
      liftEquationFinsetAfterFirst (rationalizedEquationFinset equations) := by
  classical
  ext f
  simp only [rationalizedEquationFinset, liftEquationFinsetAfterFirst,
    Finset.mem_image, Finset.mem_map]
  constructor
  · rintro ⟨g, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) h, ⟨h, hh, rfl⟩, ?_⟩
    simp [liftPolynomialAfterFirstEmbedding, liftPolynomialAfterFirst,
      MvPolynomial.map_rename]
  · rintro ⟨g, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨liftPolynomialAfterFirst h, ⟨h, hh, rfl⟩, ?_⟩
    simp [liftPolynomialAfterFirstEmbedding, liftPolynomialAfterFirst,
      MvPolynomial.map_rename]

/-- The rational ideal of the lifted twelve-variable family is exactly the
consecutively indexed projective cone ideal. -/
theorem finiteEquationIdeal_lift_rationalized
    (equations : Finset (MvPolynomial (Fin 12) ℤ)) :
    finiteEquationIdeal
        (rationalizedEquationFinset
          (liftEquationFinsetAfterFirst equations)) =
      projectiveConeFinIdeal ℚ 11
        (finiteEquationIdeal (rationalizedEquationFinset equations)) := by
  rw [rationalizedEquationFinset_liftEquationFinsetAfterFirst]
  unfold finiteEquationIdeal projectiveConeFinIdeal
  unfold projectiveConeIdealExtension
  change Ideal.span
      (↑(liftEquationFinsetAfterFirst
        (rationalizedEquationFinset equations)) :
          Set (MvPolynomial (Fin 13) ℚ)) =
    Ideal.map
      (MvPolynomial.renameEquiv ℚ
        (_root_.finSuccEquiv (11 + 1)).symm).toRingEquiv.toRingHom
      (Ideal.map (MvPolynomial.rename some)
        (Ideal.span
          (↑(rationalizedEquationFinset equations) :
            Set (MvPolynomial (Fin 12) ℚ))))
  rw [Ideal.map_span, Ideal.map_span]
  apply congrArg Ideal.span
  unfold liftEquationFinsetAfterFirst
  rw [Finset.coe_map, Set.image_image]
  apply congrArg (fun φ : MvPolynomial (Fin 12) ℚ →
      MvPolynomial (Fin 13) ℚ ↦
    φ '' (↑(rationalizedEquationFinset equations) :
      Set (MvPolynomial (Fin 12) ℚ)))
  funext f
  change liftPolynomialAfterFirst f = _
  unfold liftPolynomialAfterFirst
  change MvPolynomial.rename Fin.succ f =
    MvPolynomial.rename (_root_.finSuccEquiv 12).symm
      (MvPolynomial.rename some f)
  rw [MvPolynomial.rename_rename]
  change MvPolynomial.rename Fin.succ f =
    MvPolynomial.rename
      ((fun i ↦ (_root_.finSuccEquiv 12).symm (some i))) f
  congr 1

/-- Polynomial extension by the cone coordinate is prime exactly when its
coefficient ideal is prime.  The forward implication is obtained by the
explicit equivalence with a univariate polynomial ring. -/
theorem projectiveConeIdealExtension_isPrime_iff
    (K : Type*) [Field K] {σ : Type*}
    (I : Ideal (MvPolynomial σ K)) :
    (projectiveConeIdealExtension I).IsPrime ↔ I.IsPrime := by
  constructor
  · intro hcone
    letI : (projectiveConeIdealExtension I).IsPrime := hcone
    have hmapped :
        ((projectiveConeIdealExtension I).map
          (MvPolynomial.optionEquivLeft K σ)).IsPrime :=
      Ideal.map_isPrime_of_equiv (MvPolynomial.optionEquivLeft K σ)
    rw [map_projectiveConeIdealExtension_optionEquivLeft] at hmapped
    exact (Ideal.isPrime_map_C_iff_isPrime I).mp hmapped
  · exact projectiveConeIdealExtension_isPrime I

/-- The same prime equivalence after reindexing the cone coordinates by
`Fin`. -/
theorem projectiveConeFinIdeal_isPrime_iff
    (K : Type*) [Field K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) :
    (projectiveConeFinIdeal K N I).IsPrime ↔ I.IsPrime := by
  constructor
  · intro hcone
    let e := MvPolynomial.renameEquiv K
      (_root_.finSuccEquiv (N + 1)).symm
    letI : (projectiveConeFinIdeal K N I).IsPrime := hcone
    have hback :
        ((projectiveConeFinIdeal K N I).map e.symm).IsPrime :=
      Ideal.map_isPrime_of_equiv e.symm
    have hundo :
        (projectiveConeFinIdeal K N I).map e.symm =
          projectiveConeIdealExtension I := by
      unfold projectiveConeFinIdeal
      exact Ideal.map_of_equiv e.toRingEquiv
    rw [hundo] at hback
    exact (projectiveConeIdealExtension_isPrime_iff K I).mp hback
  · exact projectiveConeFinIdeal_isPrime K N I

/-- Coefficient extension commutes with adjoining the projective cone
coordinate. -/
theorem map_projectiveConeIdealExtension_coefficients
    (E : Type*) [Field E] [Algebra ℚ E]
    {σ : Type*} (I : Ideal (MvPolynomial σ ℚ)) :
    (projectiveConeIdealExtension I).map
        (MvPolynomial.map (algebraMap ℚ E)) =
      projectiveConeIdealExtension
        (I.map (MvPolynomial.map (algebraMap ℚ E))) := by
  unfold projectiveConeIdealExtension
  change Ideal.map (MvPolynomial.map (algebraMap ℚ E))
      (Ideal.map (MvPolynomial.rename some).toRingHom I) =
    Ideal.map (MvPolynomial.rename some).toRingHom
      (Ideal.map (MvPolynomial.map (algebraMap ℚ E)) I)
  rw [Ideal.map_map, Ideal.map_map]
  apply congrArg (fun φ : MvPolynomial σ ℚ →+*
      MvPolynomial (Option σ) E ↦ I.map φ)
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    simp

/-- Coefficient extension also commutes with the consecutively indexed cone
ideal. -/
theorem map_projectiveConeFinIdeal_coefficients
    (E : Type*) [Field E] [Algebra ℚ E]
    (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    (projectiveConeFinIdeal ℚ N I).map
        (MvPolynomial.map (algebraMap ℚ E)) =
      projectiveConeFinIdeal E N
        (I.map (MvPolynomial.map (algebraMap ℚ E))) := by
  unfold projectiveConeFinIdeal
  change Ideal.map (MvPolynomial.map (algebraMap ℚ E))
      (Ideal.map
        (MvPolynomial.renameEquiv ℚ
          (_root_.finSuccEquiv (N + 1)).symm).toRingEquiv.toRingHom
        (projectiveConeIdealExtension I)) =
    Ideal.map
      (MvPolynomial.renameEquiv E
        (_root_.finSuccEquiv (N + 1)).symm).toRingEquiv.toRingHom
      (projectiveConeIdealExtension
        (I.map (MvPolynomial.map (algebraMap ℚ E))))
  rw [← map_projectiveConeIdealExtension_coefficients E I]
  rw [Ideal.map_map, Ideal.map_map]
  apply congrArg (fun φ : MvPolynomial (Option (Fin (N + 1))) ℚ →+*
      MvPolynomial (Fin ((N + 1) + 1)) E ↦
    (projectiveConeIdealExtension I).map φ)
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    simp

/-- Geometric primeness of a consecutively indexed projective cone is
equivalent to geometric primeness of its base. -/
theorem geometricallyPrime_projectiveConeFinIdeal_iff
    (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    GeometricallyPrimeMvPolynomialIdeal (projectiveConeFinIdeal ℚ N I) ↔
      GeometricallyPrimeMvPolynomialIdeal I := by
  constructor
  · intro h E _ _
    have hcone :
        ((projectiveConeFinIdeal ℚ N I).map
          (MvPolynomial.map (algebraMap ℚ E))).IsPrime := h E
    rw [map_projectiveConeFinIdeal_coefficients E N I] at hcone
    exact (projectiveConeFinIdeal_isPrime_iff E N
      (I.map (MvPolynomial.map (algebraMap ℚ E)))).mp hcone
  · intro h E _ _
    rw [map_projectiveConeFinIdeal_coefficients E N I]
    exact (projectiveConeFinIdeal_isPrime_iff E N
      (I.map (MvPolynomial.map (algebraMap ℚ E)))).mpr (h E)

/-- The actual rational homogeneous ideal cut out by the lower integral
equations. -/
def isolatedVertexLowerRationalIdeal
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    Ideal (MvPolynomial (Fin 12) ℚ) :=
  finiteEquationIdeal (rationalizedEquationFinset lowerEquations)

/-- Exact ideal identity supplied by a literal first-coordinate equation
reduction. -/
theorem sourceIdeal_map_rationalPolynomialEquiv_eq_projectiveCone
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (equationsI : Finset (MvPolynomial (Fin 13) ℤ))
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hideal : Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
        (Ideal.span (equationsI : Set (MvPolynomial (Fin 13) ℤ))) = I)
    (hfamily : U.transformEquationFinset equationsI =
      liftEquationFinsetAfterFirst lowerEquations) :
    I.map U.rationalPolynomialEquiv =
      projectiveConeFinIdeal ℚ 11
        (isolatedVertexLowerRationalIdeal lowerEquations) := by
  have hrational :
      finiteEquationIdeal (rationalizedEquationFinset equationsI) = I :=
    (finiteEquationIdeal_rationalized_eq_map_span equationsI).trans hideal
  calc
    I.map U.rationalPolynomialEquiv =
        (finiteEquationIdeal
          (rationalizedEquationFinset equationsI)).map
            U.rationalPolynomialEquiv := by rw [hrational]
    _ = finiteEquationIdeal
          (rationalizedEquationFinset
            (U.transformEquationFinset equationsI)) :=
      (finiteEquationIdeal_transform_rationalized U equationsI).symm
    _ = finiteEquationIdeal
          (rationalizedEquationFinset
            (liftEquationFinsetAfterFirst lowerEquations)) := by rw [hfamily]
    _ = projectiveConeFinIdeal ℚ 11
          (isolatedVertexLowerRationalIdeal lowerEquations) :=
      finiteEquationIdeal_lift_rationalized lowerEquations

/-- Geometric primeness of the source passes, without any additional
geometric premise, to the literal lower-equation ideal in an exact
first-coordinate reduction. -/
theorem lowerIdeal_geometricallyPrime_of_source
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (equationsI : Finset (MvPolynomial (Fin 13) ℤ))
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hideal : Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
        (Ideal.span (equationsI : Set (MvPolynomial (Fin 13) ℤ))) = I)
    (hfamily : U.transformEquationFinset equationsI =
      liftEquationFinsetAfterFirst lowerEquations)
    (hGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal I) :
    GeometricallyPrimeMvPolynomialIdeal
      (isolatedVertexLowerRationalIdeal lowerEquations) := by
  let J := isolatedVertexLowerRationalIdeal lowerEquations
  have hcone : I.map U.rationalPolynomialEquiv =
      projectiveConeFinIdeal ℚ 11 J :=
    sourceIdeal_map_rationalPolynomialEquiv_eq_projectiveCone
      I equationsI U lowerEquations hideal hfamily
  have htransformed : GeometricallyPrimeMvPolynomialIdeal
      (I.map U.rationalPolynomialEquiv) :=
    (geometricallyPrime_map_rationalPolynomialEquiv_iff U I).mpr
      hGeometricallyPrime
  have hconeGeometric : GeometricallyPrimeMvPolynomialIdeal
      (projectiveConeFinIdeal ℚ 11 J) := by
    rw [← hcone]
    exact htransformed
  exact (geometricallyPrime_projectiveConeFinIdeal_iff 11 J).mp
    hconeGeometric

/-- The quotient of the consecutively indexed cone ideal is literally a
polynomial ring in the vertex coordinate over the quotient by the lower
ideal. -/
def projectiveConeFinQuotientRingEquiv
    (J : Ideal (MvPolynomial (Fin 12) ℚ)) :
    (MvPolynomial (Fin 13) ℚ ⧸ projectiveConeFinIdeal ℚ 11 J) ≃+*
      Polynomial (MvPolynomial (Fin 12) ℚ ⧸ J) :=
  (renameQuotientAlgEquiv ℚ (_root_.finSuccEquiv 12).symm
      (projectiveConeIdealExtension J)).symm.toRingEquiv.trans
    (projectiveConeQuotientRingEquiv J)

/-- Combining the exact ideal identity with the coordinate automorphism
gives the promised `A¹`-product decomposition of the original affine cone's
coordinate ring. -/
def isolatedVertexSourceQuotientRingEquiv
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (U : IntegralUnimodularChange 13)
    (J : Ideal (MvPolynomial (Fin 12) ℚ))
    (hcone : I.map U.rationalPolynomialEquiv =
      projectiveConeFinIdeal ℚ 11 J) :
    (MvPolynomial (Fin 13) ℚ ⧸ I) ≃+*
      Polynomial (MvPolynomial (Fin 12) ℚ ⧸ J) :=
  (Ideal.quotientEquivAlg I (I.map U.rationalPolynomialEquiv)
      U.rationalPolynomialEquiv rfl).toRingEquiv.trans
    ((Ideal.quotientEquivAlgOfEq ℚ hcone).toRingEquiv.trans
      (projectiveConeFinQuotientRingEquiv J))

/-- Lift an indexed equation family by adjoining an unused first
coordinate. -/
def liftPolynomialFamilyAfterFirst {c n : ℕ}
    (F : Fin c → MvPolynomial (Fin n) ℤ) :
    Fin c → MvPolynomial (Fin (n + 1)) ℤ :=
  fun i ↦ liftPolynomialAfterFirst (F i)

@[simp]
theorem pderiv_zero_liftPolynomialAfterFirst {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) :
    MvPolynomial.pderiv (0 : Fin (n + 1))
      (liftPolynomialAfterFirst f) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  obtain ⟨i, _hi, hisucc⟩ :=
    MvPolynomial.mem_vars_rename Fin.succ f hmem
  exact Fin.succ_ne_zero i hisucc

@[simp]
theorem pderiv_succ_liftPolynomialAfterFirst {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (j : Fin n) :
    MvPolynomial.pderiv j.succ (liftPolynomialAfterFirst f) =
      liftPolynomialAfterFirst (MvPolynomial.pderiv j f) := by
  exact MvPolynomial.pderiv_rename (Fin.succ_injective n) j f

@[simp]
theorem integralJacobianMatrix_lift_zero {c n : ℕ}
    (F : Fin c → MvPolynomial (Fin n) ℤ)
    (x : IntVector (n + 1)) (i : Fin c) :
    integralJacobianMatrix (liftPolynomialFamilyAfterFirst F) x i 0 = 0 := by
  simp [integralJacobianMatrix, liftPolynomialFamilyAfterFirst]

@[simp]
theorem integralJacobianMatrix_lift_succ {c n : ℕ}
    (F : Fin c → MvPolynomial (Fin n) ℤ)
    (x : IntVector (n + 1)) (i : Fin c) (j : Fin n) :
    integralJacobianMatrix (liftPolynomialFamilyAfterFirst F) x i j.succ =
      integralJacobianMatrix F (dropFirstIntVector x) i j := by
  simp only [integralJacobianMatrix, liftPolynomialFamilyAfterFirst,
    pderiv_succ_liftPolynomialAfterFirst, eval_liftPolynomialAfterFirst]
  change MvPolynomial.eval (fun k ↦ x k.succ)
      (MvPolynomial.pderiv j (F i)) =
    MvPolynomial.eval (fun k ↦ x k.succ)
      (MvPolynomial.pderiv j (F i))
  rfl

/-- Adjoining an unused coordinate does not change the Jacobian rank.  This
is the literal matrix statement behind smoothness preservation for the
`A¹` product. -/
theorem rank_integralJacobianMatrix_liftPolynomialFamilyAfterFirst
    {c n : ℕ} (F : Fin c → MvPolynomial (Fin n) ℤ)
    (x : IntVector (n + 1)) :
    ((integralJacobianMatrix (liftPolynomialFamilyAfterFirst F) x).map
        (Int.castRingHom ℚ)).rank =
      ((integralJacobianMatrix F (dropFirstIntVector x)).map
        (Int.castRingHom ℚ)).rank := by
  let A := (integralJacobianMatrix
    (liftPolynomialFamilyAfterFirst F) x).map (Int.castRingHom ℚ)
  let B := (integralJacobianMatrix F
    (dropFirstIntVector x)).map (Int.castRingHom ℚ)
  have hzero : A.col 0 = 0 := by
    funext i
    simp [A]
  have hsucc (j : Fin n) : A.col j.succ = B.col j := by
    funext i
    simp [A, B]
  have hspan :
      Submodule.span ℚ (Set.range A.col) =
        Submodule.span ℚ (Set.range B.col) := by
    apply le_antisymm
    · apply Submodule.span_le.2
      intro v hv
      obtain ⟨j, rfl⟩ := hv
      refine Fin.cases ?_ (fun k ↦ ?_) j
      · rw [hzero]
        exact Submodule.zero_mem _
      · rw [hsucc]
        exact Submodule.subset_span ⟨k, rfl⟩
    · apply Submodule.span_le.2
      intro v hv
      obtain ⟨j, rfl⟩ := hv
      rw [← hsucc]
      exact Submodule.subset_span ⟨j.succ, rfl⟩
  rw [Matrix.rank_eq_finrank_span_cols,
    Matrix.rank_eq_finrank_span_cols, hspan]

/-- In the twelve-variable quotient used in the rank-seven branch, the
regularity rank condition is therefore exactly the rank condition for the
lifted thirteen-variable cylinder equations. -/
theorem isQuotientJacobianRegularAt_iff_lifted_rank
    (equations : Finset (MvPolynomial (Fin 12) ℤ))
    (x : IntVector 13) :
    IsQuotientJacobianRegularAt equations (dropFirstIntVector x) ↔
      7 ≤ ((integralJacobianMatrix
        (liftPolynomialFamilyAfterFirst (indexedFinsetFamily equations)) x).map
          (Int.castRingHom ℚ)).rank := by
  unfold IsQuotientJacobianRegularAt
  rw [rank_integralJacobianMatrix_liftPolynomialFamilyAfterFirst]

/-- Jacobian rank depends only on the set of equations in the indexed
family, not on its finite indexing. -/
theorem rank_integralJacobianMatrix_eq_of_range_eq
    {c d n : ℕ}
    (F : Fin c → MvPolynomial (Fin n) ℤ)
    (G : Fin d → MvPolynomial (Fin n) ℤ)
    (x : IntVector n) (hrange : Set.range F = Set.range G) :
    ((integralJacobianMatrix F x).map (Int.castRingHom ℚ)).rank =
      ((integralJacobianMatrix G x).map (Int.castRingHom ℚ)).rank := by
  let A := (integralJacobianMatrix F x).map (Int.castRingHom ℚ)
  let B := (integralJacobianMatrix G x).map (Int.castRingHom ℚ)
  have hrows : Set.range A.transpose.col = Set.range B.transpose.col := by
    ext row
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hij⟩ := Set.ext_iff.mp hrange (F i) |>.mp ⟨i, rfl⟩
      refine ⟨j, ?_⟩
      funext k
      simp [A, B, integralJacobianMatrix, hij]
    · rintro ⟨j, rfl⟩
      obtain ⟨i, hij⟩ := Set.ext_iff.mp hrange (G j) |>.mpr ⟨j, rfl⟩
      refine ⟨i, ?_⟩
      funext k
      simp [A, B, integralJacobianMatrix, hij]
  calc
    A.rank = A.transpose.rank := (Matrix.rank_transpose A).symm
    _ = Module.finrank ℚ
        (Submodule.span ℚ (Set.range A.transpose.col)) :=
      Matrix.rank_eq_finrank_span_cols A.transpose
    _ = Module.finrank ℚ
        (Submodule.span ℚ (Set.range B.transpose.col)) := by rw [hrows]
    _ = B.transpose.rank :=
      (Matrix.rank_eq_finrank_span_cols B.transpose).symm
    _ = B.rank := Matrix.rank_transpose B

/-- The canonical indexing of a lifted finite equation set has the same
Jacobian rank as lifting the canonical indexing of the lower set. -/
theorem rank_integralJacobianMatrix_indexed_liftEquationFinset
    {n : ℕ} (equations : Finset (MvPolynomial (Fin n) ℤ))
    (x : IntVector (n + 1)) :
    ((integralJacobianMatrix
        (indexedFinsetFamily (liftEquationFinsetAfterFirst equations)) x).map
      (Int.castRingHom ℚ)).rank =
    ((integralJacobianMatrix
        (liftPolynomialFamilyAfterFirst (indexedFinsetFamily equations)) x).map
      (Int.castRingHom ℚ)).rank := by
  apply rank_integralJacobianMatrix_eq_of_range_eq
  ext f
  constructor
  · intro hf
    rw [range_indexedFinsetFamily] at hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hf
    have hgrange : g ∈ Set.range (indexedFinsetFamily equations) := by
      rw [range_indexedFinsetFamily]
      exact hg
    obtain ⟨i, rfl⟩ := hgrange
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    rw [range_indexedFinsetFamily]
    apply Finset.mem_map.mpr
    exact ⟨indexedFinsetFamily equations i,
      (Set.ext_iff.mp (range_indexedFinsetFamily equations)
        (indexedFinsetFamily equations i)).mp ⟨i, rfl⟩, rfl⟩

/-- The same rank statement written for the actual transformed source
family occurring in the exact lower-equation reduction. -/
theorem isQuotientJacobianRegularAt_iff_transformedEquationFinset_rank
    (equationsI : Finset (MvPolynomial (Fin 13) ℤ))
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hfamily : U.transformEquationFinset equationsI =
      liftEquationFinsetAfterFirst lowerEquations)
    (x : IntVector 13) :
    IsQuotientJacobianRegularAt lowerEquations (dropFirstIntVector x) ↔
      7 ≤ ((integralJacobianMatrix
        (indexedFinsetFamily (U.transformEquationFinset equationsI)) x).map
          (Int.castRingHom ℚ)).rank := by
  rw [hfamily]
  rw [rank_integralJacobianMatrix_indexed_liftEquationFinset]
  exact isQuotientJacobianRegularAt_iff_lifted_rank lowerEquations x

/-- There is no nonzero primitive integral direction representing a
rational point of the geometric projective vertex.  For a rational
projective variety this is equivalent, by rational descent for a linear
vertex, to saying that the geometric projective vertex is empty. -/
def HasNoPrimitiveRationalGeometricProjectiveVertex {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) ℚ)) : Prop :=
  ∀ h : IntVector m, PrimitiveDirection h →
    ¬ LiesInGeometricProjectiveVertex h I

/-- The displayed rational vertex line is the only rational projective
vertex line of the source.  Proportionality is stated over `ℚ`, so it is
independent of the choice of primitive integral representative. -/
def HasUniqueRationalGeometricProjectiveVertexLine {m : ℕ}
    (h : IntVector m) (I : Ideal (MvPolynomial (Fin m) ℚ)) : Prop :=
  LiesInGeometricProjectiveVertex h I ∧
    ∀ v : IntVector m, LiesInGeometricProjectiveVertex v I →
      ∃ a : ℚ, ∀ i, (v i : ℚ) = a * (h i : ℚ)

/-- Coefficientwise inclusion of an integral vector in rational affine
space. -/
def rationalVectorOfInt {m : ℕ} (v : IntVector m) : Fin m → ℚ :=
  fun i ↦ (v i : ℚ)

/-- Integral matrix multiplication commutes with coefficientwise inclusion
in `ℚ`. -/
theorem rationalVectorOfInt_mulVec {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℤ) (v : IntVector m) :
    rationalVectorOfInt (Matrix.mulVec A v) =
      Matrix.mulVec (A.map (Int.castRingHom ℚ)) (rationalVectorOfInt v) := by
  funext i
  simp [rationalVectorOfInt, Matrix.mulVec, dotProduct]

namespace StandardAG

/-- A homogeneous unimodular linear change preserves the projective
dimension, degree, saturation and rational integrality certificate. -/
def IntegralProjectiveVarietyUnimodularInvariance : Prop :=
  ∀ (M r d : ℕ) (I : Ideal (MvPolynomial (Fin (M + 1)) ℚ))
      (U : IntegralUnimodularChange (M + 1)),
    Published.IsIntegralProjectiveVariety (N := M) I r d →
      Published.IsIntegralProjectiveVariety (N := M)
        (I.map U.rationalPolynomialEquiv) r d

/-- The base of an integral projective cone of dimension `r+1` and degree
`d` is an integral projective variety of dimension `r` and the same degree.
This is the standard Hilbert-series identity together with contraction of
homogeneity and saturation from a polynomial extension. -/
def IntegralProjectiveConeBaseGeometryDescent : Prop :=
  ∀ (N r d : ℕ) (J : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    Published.IsIntegralProjectiveVariety (N := N + 1)
      (projectiveConeFinIdeal ℚ N J) (r + 1) d →
        Published.IsIntegralProjectiveVariety (N := N) J r d

/-- Textbook projective-cone descent for the projective Hilbert data.  A
homogeneous linear coordinate change identifies the source with the
projective cone over `J`; the Hilbert-polynomial identity for a cone lowers
projective dimension by one and preserves degree, while saturation and
homogeneity descend to the base.  Primality and geometric primality are not
part of this premise: they are proved above from explicit polynomial-ring
maps.

This proposition packages only standard projective geometry; in particular
it contains no height or point-counting estimate. -/
def UnimodularProjectiveConeGeometryDescent : Prop :=
  ∀ (N r d : ℕ)
      (I : Ideal (MvPolynomial (Fin ((N + 1) + 1)) ℚ))
      (J : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
      (U : IntegralUnimodularChange ((N + 1) + 1)),
    Published.IsIntegralProjectiveVariety (N := N + 1) I (r + 1) d →
    I.map U.rationalPolynomialEquiv = projectiveConeFinIdeal ℚ N J →
      Published.IsIntegralProjectiveVariety (N := N) J r d

/-- Projective vertices are preserved by the displayed homogeneous
unimodular coordinate change.  This is the evaluation identity for an
invertible linear substitution over the fixed algebraic closure. -/
def ProjectiveVertexUnimodularTransport : Prop :=
  ∀ (m : ℕ) (I : Ideal (MvPolynomial (Fin m) ℚ))
      (U : IntegralUnimodularChange m) (v : IntVector m),
    LiesInGeometricProjectiveVertex
        (Matrix.mulVec U.forward v) (I.map U.rationalPolynomialEquiv) ↔
      LiesInGeometricProjectiveVertex v I

/-- A vertex direction of the base of a projective cone remains a vertex
direction after a zero is prepended in the cone coordinate. -/
def ProjectiveConeBaseVertexLift : Prop :=
  ∀ (N : ℕ) (J : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
      (v : IntVector (N + 1)),
    LiesInGeometricProjectiveVertex v J →
      LiesInGeometricProjectiveVertex
        (prependFirstIntVector 0 v) (projectiveConeFinIdeal ℚ N J)

/-- Textbook vertex correspondence for a projective cone.  After the source
vertex line has been sent to the new cone coordinate, any rational vertex of
the base would lift to a second rational vertex line of the cone. -/
def UniqueVertexProjectiveConeBaseHasNoVertex : Prop :=
  ∀ (N : ℕ)
      (I : Ideal (MvPolynomial (Fin ((N + 1) + 1)) ℚ))
      (J : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
      (U : IntegralUnimodularChange ((N + 1) + 1))
      (h : IntVector ((N + 1) + 1)),
    Matrix.mulVec U.forward h = firstCoordinateIntDirection →
    I.map U.rationalPolynomialEquiv = projectiveConeFinIdeal ℚ N J →
    HasUniqueRationalGeometricProjectiveVertexLine h I →
      HasNoPrimitiveRationalGeometricProjectiveVertex J

/-- A positive-dimensional geometrically integral projective variety of
degree one is a projective linear space.  Such a variety has a nonempty
rational projective vertex.  We expose only the contrapositive needed here. -/
def VertexFreeIntegralProjectiveVarietyHasDegreeAtLeastTwo : Prop :=
  ∀ (N r d : ℕ) (J : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    0 < r →
    GeometricallyPrimeMvPolynomialIdeal J →
    Published.IsIntegralProjectiveVariety (N := N) J r d →
    HasNoPrimitiveRationalGeometricProjectiveVertex J →
      2 ≤ d

end StandardAG

/-- The previously packaged coordinate-change/cone-descent statement is a
formal composite of the two narrower textbook propositions. -/
theorem unimodularProjectiveConeGeometryDescent_of_invariance_and_cone
    (hinvariance : StandardAG.IntegralProjectiveVarietyUnimodularInvariance)
    (hconeBase : StandardAG.IntegralProjectiveConeBaseGeometryDescent) :
    StandardAG.UnimodularProjectiveConeGeometryDescent := by
  intro N r d I J U hI hcone
  have htransformed := hinvariance (N + 1) (r + 1) d I U hI
  rw [hcone] at htransformed
  exact hconeBase N r d J htransformed

/-- The packaged cone/base vertex implication follows from the two literal
textbook functoriality statements above.  The rest is rational linear
algebra: a nonzero base direction gives a cone direction independent of the
distinguished first direction. -/
theorem uniqueVertexProjectiveConeBaseHasNoVertex_of_transport
    (hcoordinate : StandardAG.ProjectiveVertexUnimodularTransport)
    (hconeLift : StandardAG.ProjectiveConeBaseVertexLift) :
    StandardAG.UniqueVertexProjectiveConeBaseHasNoVertex := by
  intro N I J U h hforward hcone hisolated
  intro v hprimitive hv
  let w : IntVector ((N + 1) + 1) := prependFirstIntVector 0 v
  let u : IntVector ((N + 1) + 1) := Matrix.mulVec U.inverse w
  have hforwardU : Matrix.mulVec U.forward u = w := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec, U.forward_mul_inverse, Matrix.one_mulVec]
  have hwCone : LiesInGeometricProjectiveVertex w
      (projectiveConeFinIdeal ℚ N J) := hconeLift N J v hv
  have hwMapped : LiesInGeometricProjectiveVertex w
      (I.map U.rationalPolynomialEquiv) := by
    rw [hcone]
    exact hwCone
  have hu : LiesInGeometricProjectiveVertex u I := by
    apply (hcoordinate ((N + 1) + 1) I U u).mp
    rw [hforwardU]
    exact hwMapped
  obtain ⟨a, hua⟩ := hisolated.2 u hu
  have huQ : rationalVectorOfInt u =
      a • rationalVectorOfInt h := by
    funext i
    simpa [rationalVectorOfInt, Pi.smul_apply] using hua i
  have hwQ : rationalVectorOfInt w =
      a • rationalVectorOfInt firstCoordinateIntDirection := by
    calc
      rationalVectorOfInt w =
          rationalVectorOfInt (Matrix.mulVec U.forward u) := by
        rw [hforwardU]
      _ = Matrix.mulVec (U.forward.map (Int.castRingHom ℚ))
          (rationalVectorOfInt u) :=
        rationalVectorOfInt_mulVec U.forward u
      _ = Matrix.mulVec (U.forward.map (Int.castRingHom ℚ))
          (a • rationalVectorOfInt h) := by rw [huQ]
      _ = a • Matrix.mulVec (U.forward.map (Int.castRingHom ℚ))
          (rationalVectorOfInt h) := by
        rw [Matrix.mulVec_smul]
      _ = a • rationalVectorOfInt (Matrix.mulVec U.forward h) := by
        rw [rationalVectorOfInt_mulVec]
      _ = a • rationalVectorOfInt firstCoordinateIntDirection := by
        rw [hforward]
  obtain ⟨j, hj⟩ := hprimitive.exists_ne_zero
  have hjQ : (v j : ℚ) = 0 := by
    have := congrFun hwQ j.succ
    simpa [w, rationalVectorOfInt, Pi.smul_apply] using this
  apply hj
  exact_mod_cast hjQ

/-- Complete geometry output of the literal isolated-vertex reduction.
The lower ideal is the ideal generated by the displayed lower integral
equations, not an abstract isomorphic replacement.  The quotient has the
same degree as the source, is geometrically integral and nonlinear, and has
no rational projective vertex; the exact product decomposition is returned
simultaneously. -/
theorem isolatedVertex_lowerIdeal_geometry
    (hconeGeometry : StandardAG.UnimodularProjectiveConeGeometryDescent)
    (hvertexDescent : StandardAG.UniqueVertexProjectiveConeBaseHasNoVertex)
    (hdegreeOne :
      StandardAG.VertexFreeIntegralProjectiveVarietyHasDegreeAtLeastTwo)
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (equationsI : Finset (MvPolynomial (Fin 13) ℤ))
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (h : IntVector 13) (degree degreeBound : ℕ)
    (hideal : Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
        (Ideal.span (equationsI : Set (MvPolynomial (Fin 13) ℤ))) = I)
    (hforward : Matrix.mulVec U.forward h = firstCoordinateIntDirection)
    (hfamily : U.transformEquationFinset equationsI =
      liftEquationFinsetAfterFirst lowerEquations)
    (hGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal I)
    (hprojective : Published.IsIntegralProjectiveVariety
      (N := 12) I 5 degree)
    (hisolated : HasUniqueRationalGeometricProjectiveVertexLine h I)
    (hdegreeBound : degree ≤ degreeBound) :
    let J := isolatedVertexLowerRationalIdeal lowerEquations
    GeometricallyPrimeMvPolynomialIdeal J ∧
      Published.IsIntegralProjectiveVariety (N := 11) J 4 degree ∧
      2 ≤ degree ∧ degree ≤ degreeBound ∧
      HasNoPrimitiveRationalGeometricProjectiveVertex J ∧
      Nonempty ((MvPolynomial (Fin 13) ℚ ⧸ I) ≃+*
        Polynomial (MvPolynomial (Fin 12) ℚ ⧸ J)) := by
  dsimp only
  let J := isolatedVertexLowerRationalIdeal lowerEquations
  have hcone : I.map U.rationalPolynomialEquiv =
      projectiveConeFinIdeal ℚ 11 J :=
    sourceIdeal_map_rationalPolynomialEquiv_eq_projectiveCone
      I equationsI U lowerEquations hideal hfamily
  have hJgeometric : GeometricallyPrimeMvPolynomialIdeal J :=
    lowerIdeal_geometricallyPrime_of_source I equationsI U lowerEquations
      hideal hfamily hGeometricallyPrime
  have hJprojective :=
    hconeGeometry 11 4 degree I J U hprojective hcone
  have hJvertexFree : HasNoPrimitiveRationalGeometricProjectiveVertex J :=
    hvertexDescent 11 I J U h hforward hcone hisolated
  have hJnonlinear : 2 ≤ degree :=
    hdegreeOne 11 4 degree J (by omega) hJgeometric hJprojective hJvertexFree
  exact ⟨hJgeometric, hJprojective, hJnonlinear, hdegreeBound,
    hJvertexFree, ⟨isolatedVertexSourceQuotientRingEquiv I U J hcone⟩⟩

/-- Strict source-section form of `isolatedVertex_lowerIdeal_geometry`.
Starting from the literal rational ideal of the displayed thirteen-variable
equations, it produces actual integral equations for the quotient fourfold
and all of the projective-geometric conclusions attached to precisely that
ideal. -/
theorem exists_strictIsolatedVertex_lowerIdeal_geometry
    (hvertexTheorem : StandardAG.ProjectiveVertexIdealTranslationStability)
    (hcylinder : StandardAG.TranslationStableHomogeneousIdealCylinderGenerators)
    (hcompletion : StandardLattice.PrimitiveDirectionUnimodularCompletion)
    (hconeGeometry : StandardAG.UnimodularProjectiveConeGeometryDescent)
    (hvertexDescent : StandardAG.UniqueVertexProjectiveConeBaseHasNoVertex)
    (hdegreeOne :
      StandardAG.VertexFreeIntegralProjectiveVarietyHasDegreeAtLeastTwo)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree degreeBound : ℕ)
    (hprojective : Published.IsIntegralProjectiveVariety
      (N := 12) (rationalDepthSevenEquationIdeal equations) 5 degree)
    (hGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal
      (rationalDepthSevenEquationIdeal equations))
    (h : IntVector 13) (hprimitive : PrimitiveDirection h)
    (hisolated : HasUniqueRationalGeometricProjectiveVertexLine h
      (rationalDepthSevenEquationIdeal equations))
    (hdegreeBound : degree ≤ degreeBound) :
    ∃ (equationsI : Finset (MvPolynomial (Fin 13) ℤ))
        (U : IntegralUnimodularChange 13)
        (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)),
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
          (Ideal.span (equationsI : Set (MvPolynomial (Fin 13) ℤ))) =
            rationalDepthSevenEquationIdeal equations ∧
      Matrix.mulVec U.forward h = firstCoordinateIntDirection ∧
      U.transformEquationFinset equationsI =
          liftEquationFinsetAfterFirst lowerEquations ∧
      (∀ g ∈ lowerEquations, ∃ e : ℕ, g.IsHomogeneous e) ∧
      let J := isolatedVertexLowerRationalIdeal lowerEquations
      GeometricallyPrimeMvPolynomialIdeal J ∧
        Published.IsIntegralProjectiveVariety (N := 11) J 4 degree ∧
        2 ≤ degree ∧ degree ≤ degreeBound ∧
        HasNoPrimitiveRationalGeometricProjectiveVertex J ∧
        Nonempty ((MvPolynomial (Fin 13) ℚ ⧸
            rationalDepthSevenEquationIdeal equations) ≃+*
          Polynomial (MvPolynomial (Fin 12) ℚ ⧸ J)) := by
  obtain ⟨equationsI, U, lowerEquations, hideal, hforward, hfamily,
      hhomogeneous, _hpointReduction⟩ :=
    exists_strictIsolatedVertex_affineQuotientReduction
      hvertexTheorem hcylinder hcompletion equations degree hprojective
      h hprimitive hisolated.1
  refine ⟨equationsI, U, lowerEquations, hideal, hforward, hfamily,
    hhomogeneous, ?_⟩
  exact isolatedVertex_lowerIdeal_geometry
    hconeGeometry hvertexDescent hdegreeOne
    (rationalDepthSevenEquationIdeal equations) equationsI U lowerEquations
    h degree degreeBound hideal hforward hfamily hGeometricallyPrime
    hprojective hisolated hdegreeBound

end

end TranslatedDepthSeven
