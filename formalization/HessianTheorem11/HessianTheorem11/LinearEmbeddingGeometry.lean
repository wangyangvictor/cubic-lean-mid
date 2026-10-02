import HessianTheorem11.PolynomialCoordinateEquiv

/-! An injective linear embedding preserves the actual reduced affine
dimension and algebraic closedness. Everything is proved from polynomial
pullback and a linear left inverse; no geometric input is required. -/

noncomputable section
set_option maxHeartbeats 800000
namespace HessianTheorem11
open MvPolynomial

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem affineDimension_image_of_polynomial_leftInverse
    (P : τ → MvPolynomial σ GeometricField)
    (Q : σ → MvPolynomial τ GeometricField)
    (h : Function.LeftInverse (polynomialMap Q) (polynomialMap P))
    (Z : Set (σ → GeometricField)) :
    affineDimension (polynomialMap P '' Z) = affineDimension Z := by
  let f : MvPolynomial τ GeometricField →+* MvPolynomial σ GeometricField :=
    (aeval P : MvPolynomial τ GeometricField →ₐ[GeometricField]
      MvPolynomial σ GeometricField).toRingHom
  have hsurj : Function.Surjective f := by
    intro p
    refine ⟨aeval Q p, ?_⟩
    apply MvPolynomial.funext
    intro x
    change eval x (aeval P (aeval Q p)) = eval x p
    calc
      _ = eval (polynomialMap P x) (aeval Q p) := (eval_polynomialMap P x _).symm
      _ = eval (polynomialMap Q (polynomialMap P x)) p :=
        (eval_polynomialMap Q (polynomialMap P x) p).symm
      _ = eval x p := congrArg (fun y => eval y p) (h x)
  let I : Ideal (MvPolynomial σ GeometricField) := vanishingIdeal GeometricField Z
  have hI : vanishingIdeal GeometricField (polynomialMap P '' Z) = I.comap f :=
    vanishingIdeal_polynomialMap_image P Z
  unfold affineDimension
  rw [hI]
  let g : (MvPolynomial τ GeometricField ⧸ I.comap f) →+*
      (MvPolynomial σ GeometricField ⧸ I) := Ideal.quotientMap I f le_rfl
  have hg : Function.Bijective g :=
    ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective hsurj⟩
  exact ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective g hg)

theorem geometricClosure_image_of_polynomial_leftInverse
    (P : τ → MvPolynomial σ GeometricField)
    (Q : σ → MvPolynomial τ GeometricField)
    (h : Function.LeftInverse (polynomialMap Q) (polynomialMap P))
    (Z : Set (σ → GeometricField)) :
    geometricClosure (polynomialMap P '' Z) = polynomialMap P '' geometricClosure Z := by
  have himage : polynomialMap Q '' (polynomialMap P '' Z) = Z := by
    have hc : (fun x => polynomialMap Q (polynomialMap P x)) = id := funext h
    rw [Set.image_image, hc, Set.image_id]
  apply le_antisymm
  · intro y hy
    have hQ : polynomialMap Q y ∈ geometricClosure Z := by
      have hh := polynomialMap_image_closure_subset Q (polynomialMap P '' Z)
        (Set.mem_image_of_mem (polynomialMap Q) hy)
      rwa [himage] at hh
    refine ⟨polynomialMap Q y, hQ, ?_⟩
    funext j
    have hz : ∀ x ∈ polynomialMap P '' Z,
        eval x (X j - aeval Q (P j)) = 0 := by
      rintro _ ⟨x, _, rfl⟩
      rw [eval_sub, eval_X, ← eval_polynomialMap, h x]
      exact sub_self _
    have hh := geometricClosure_subset_of_polynomial_vanishes _ _ hz y hy
    rw [eval_sub, eval_X, ← eval_polynomialMap, sub_eq_zero] at hh
    exact hh.symm
  · exact polynomialMap_image_closure_subset P Z

theorem affineDimension_linearMap_image
    (L : (σ → GeometricField) →ₗ[GeometricField] (τ → GeometricField))
    (hL : Function.Injective L) (Z : Set (σ → GeometricField)) :
    affineDimension (L '' Z) = affineDimension Z := by
  obtain ⟨R, hR⟩ := L.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hL)
  have h : Function.LeftInverse (polynomialMap (linearCoordinatePolynomials R))
      (polynomialMap (linearCoordinatePolynomials L)) := by
    intro x
    simp only [polynomialMap_linearCoordinatePolynomials]
    exact LinearMap.congr_fun hR x
  simpa only [polynomialMap_linearCoordinatePolynomials] using
    affineDimension_image_of_polynomial_leftInverse
      (linearCoordinatePolynomials L) (linearCoordinatePolynomials R) h Z

theorem geometricClosure_linearMap_image
    (L : (σ → GeometricField) →ₗ[GeometricField] (τ → GeometricField))
    (hL : Function.Injective L) (Z : Set (σ → GeometricField)) :
    geometricClosure (L '' Z) = L '' geometricClosure Z := by
  obtain ⟨R, hR⟩ := L.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hL)
  have h : Function.LeftInverse (polynomialMap (linearCoordinatePolynomials R))
      (polynomialMap (linearCoordinatePolynomials L)) := by
    intro x
    simp only [polynomialMap_linearCoordinatePolynomials]
    exact LinearMap.congr_fun hR x
  simpa only [polynomialMap_linearCoordinatePolynomials] using
    geometricClosure_image_of_polynomial_leftInverse
      (linearCoordinatePolynomials L) (linearCoordinatePolynomials R) h Z

theorem algebraicallyClosedSet_linearMap_image
    (L : (σ → GeometricField) →ₗ[GeometricField] (τ → GeometricField))
    (hL : Function.Injective L) {Z : Set (σ → GeometricField)}
    (hZ : AlgebraicallyClosedSet Z) : AlgebraicallyClosedSet (L '' Z) := by
  change geometricClosure (L '' Z) = L '' Z
  rw [geometricClosure_linearMap_image L hL Z, hZ]

end HessianTheorem11
