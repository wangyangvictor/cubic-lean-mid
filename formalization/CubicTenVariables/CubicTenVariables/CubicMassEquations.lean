import CubicTenVariables.RationalEquationDimension
import CubicTenVariables.GeometryTen

/-! Literal equations for the full affine Hessian incidence and the gradient
zero locus. The incidence retains both vector variables and has no cubic-zero
condition. Their rational equation quotients have dimensions at most twelve
and five for an anisotropic ten-variable cubic. -/

noncomputable section
namespace CubicTenVariables.CubicMassEquations
open MvPolynomial HessianTheorem11

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- The ith actual equation of H_F(x)y=0. -/
def incidenceEquation (F : MvPolynomial (Fin n) R) (i : Fin n) :
    MvPolynomial (Fin n ⊕ Fin n) R :=
  ∑ j, rename Sum.inl (pderiv j (pderiv i F)) * X (Sum.inr j)

/-- The actual gradient equation, without an additional F=0 equation. -/
def gradientEquation (F : MvPolynomial (Fin n) R) (i : Fin n) :
    MvPolynomial (Fin n) R := pderiv i F

@[simp] theorem map_incidenceEquation (f : R →+* S)
    (F : MvPolynomial (Fin n) R) (i : Fin n) :
    map f (incidenceEquation F i) = incidenceEquation (map f F) i := by
  simp [incidenceEquation, map_rename, pderiv_map]

@[simp] theorem map_gradientEquation (f : R →+* S)
    (F : MvPolynomial (Fin n) R) (i : Fin n) :
    map f (gradientEquation F i) = gradientEquation (map f F) i := by
  simp [gradientEquation, pderiv_map]

@[simp] theorem eval_incidenceEquation (F : MvPolynomial (Fin n) R)
    (z : (Fin n ⊕ Fin n) → R) (i : Fin n) :
    eval z (incidenceEquation F i) =
      ((hessian F (z ∘ Sum.inl)).mulVec (z ∘ Sum.inr)) i := by
  simp [incidenceEquation, hessian, hessianPolynomial, Matrix.mulVec,
    dotProduct, eval_rename]

@[simp] theorem eval_gradientEquation (F : MvPolynomial (Fin n) R)
    (x : Fin n → R) (i : Fin n) :
    eval x (gradientEquation F i) = gradient F x i := rfl

/-- Evaluation after any coefficient reduction, including every residue ring. -/
theorem eval₂_incidenceEquation (f : R →+* S)
    (F : MvPolynomial (Fin n) R) (z : (Fin n ⊕ Fin n) → S) (i : Fin n) :
    eval₂ f z (incidenceEquation F i) =
      ((hessian (map f F) (z ∘ Sum.inl)).mulVec (z ∘ Sum.inr)) i := by
  rw [eval₂_eq_eval_map, map_incidenceEquation, eval_incidenceEquation]

theorem eval₂_gradientEquation (f : R →+* S)
    (F : MvPolynomial (Fin n) R) (x : Fin n → S) (i : Fin n) :
    eval₂ f x (gradientEquation F i) = gradient (map f F) x i := by
  rw [eval₂_eq_eval_map, map_gradientEquation, eval_gradientEquation]

theorem incidence_equations_zero_iff (f : R →+* S)
    (F : MvPolynomial (Fin n) R) (z : (Fin n ⊕ Fin n) → S) :
    (∀ i, eval₂ f z (incidenceEquation F i) = 0) ↔
      (hessian (map f F) (z ∘ Sum.inl)).mulVec (z ∘ Sum.inr) = 0 := by
  simp only [eval₂_incidenceEquation, funext_iff, Pi.zero_apply]

theorem gradient_equations_zero_iff (f : R →+* S)
    (F : MvPolynomial (Fin n) R) (x : Fin n → S) :
    (∀ i, eval₂ f x (gradientEquation F i) = 0) ↔
      gradient (map f F) x = 0 := by
  simp only [eval₂_gradientEquation, funext_iff, Pi.zero_apply]

/-- The span of a literal finite family of polynomial equations. -/
def equationIdeal {σ ι : Type*} (E : ι → MvPolynomial σ R) :
    Ideal (MvPolynomial σ R) := Ideal.span (Set.range E)

theorem map_equationIdeal {σ ι : Type*} (f : R →+* S)
    (E : ι → MvPolynomial σ R) :
    (equationIdeal E).map (map f) = equationIdeal (fun i => map f (E i)) := by
  rw [equationIdeal, Ideal.map_span]
  congr 1
  ext P
  simp

theorem mem_zeroLocus_equationIdeal {K : Type*} [Field K]
    {σ ι : Type*} (E : ι → MvPolynomial σ K) (x : σ → K) :
    x ∈ zeroLocus K (equationIdeal E) ↔ ∀ i, eval x (E i) = 0 := by
  rw [equationIdeal, zeroLocus_span]
  simp

theorem equationIdeal_ne_top_of_zero {K : Type*} [Field K]
    {σ ι : Type*} (E : ι → MvPolynomial σ K) (x : σ → K)
    (hx : ∀ i, eval x (E i) = 0) : equationIdeal E ≠ ⊤ := by
  intro he
  have hz := (mem_zeroLocus_equationIdeal E x).mpr hx
  rw [he, zeroLocus_top] at hz
  exact hz

/-- These are precisely the integral equations mapped to the rationals. -/
def rationalIncidenceIdeal (F : MvPolynomial (Fin n) ℤ) :
    Ideal (MvPolynomial (Fin n ⊕ Fin n) ℚ) :=
  equationIdeal (fun i => map (Int.castRingHom ℚ) (incidenceEquation F i))

def rationalGradientIdeal (F : MvPolynomial (Fin n) ℤ) :
    Ideal (MvPolynomial (Fin n) ℚ) :=
  equationIdeal (fun i => map (Int.castRingHom ℚ) (gradientEquation F i))

theorem rationalIncidenceIdeal_eq (F : MvPolynomial (Fin n) ℤ) :
    rationalIncidenceIdeal F =
      equationIdeal (incidenceEquation (map (Int.castRingHom ℚ) F)) := by
  simp [rationalIncidenceIdeal]

theorem rationalGradientIdeal_eq (F : MvPolynomial (Fin n) ℤ) :
    rationalGradientIdeal F =
      equationIdeal (gradientEquation (map (Int.castRingHom ℚ) F)) := by
  simp [rationalGradientIdeal]

/-- No homogeneity is needed: the right-hand incidence vector can be zero. -/
theorem rationalIncidenceIdeal_ne_top (F : MvPolynomial (Fin n) ℤ) :
    rationalIncidenceIdeal F ≠ ⊤ := by
  rw [rationalIncidenceIdeal_eq]
  apply equationIdeal_ne_top_of_zero _ 0
  intro i
  rw [eval_incidenceEquation]
  exact congrFun (Matrix.mulVec_zero _) i

theorem rationalGradientIdeal_ne_top (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) : rationalGradientIdeal F ≠ ⊤ := by
  rw [rationalGradientIdeal_eq]
  apply equationIdeal_ne_top_of_zero _ 0
  intro i
  have he := congrFun (hessian_mulVec_self (hF.map (Int.castRingHom ℚ))
    (0 : Fin n → ℚ)) i
  simp only [Matrix.mulVec_zero, Pi.zero_apply, Pi.smul_apply, nsmul_eq_mul] at he
  rw [eval_gradientEquation]
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

/-- Exact geometric zero-locus identification for the full incidence. -/
theorem incidence_zeroLocus_eq (F : MvPolynomial (Fin n) ℤ) :
    zeroLocus GeometricField ((rationalIncidenceIdeal F).map
      (map (algebraMap ℚ GeometricField))) =
      incidenceLocus (map (Int.castRingHom ℚ) F) := by
  rw [rationalIncidenceIdeal_eq, map_equationIdeal]
  ext z
  rw [mem_zeroLocus_equationIdeal]
  simp only [map_incidenceEquation, eval_incidenceEquation]
  exact funext_iff.symm

/-- Exact geometric zero-locus identification for the gradient. -/
theorem gradient_zeroLocus_eq (F : MvPolynomial (Fin n) ℤ) :
    zeroLocus GeometricField ((rationalGradientIdeal F).map
      (map (algebraMap ℚ GeometricField))) =
      singularLocus (map (Int.castRingHom ℚ) F) := by
  rw [rationalGradientIdeal_eq, map_equationIdeal]
  ext x
  rw [mem_zeroLocus_equationIdeal]
  simp only [map_gradientEquation, eval_gradientEquation]
  exact funext_iff.symm

theorem incidence_quotient_dimension_le_twelve
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ringKrullDim (MvPolynomial (Fin 10 ⊕ Fin 10) ℚ ⧸
      rationalIncidenceIdeal F) ≤ 12 := by
  rw [← RationalEquationDimension.rational_quotient_dimension_eq_geometric_zeroLocus
    _ (rationalIncidenceIdeal_ne_top F), incidence_zeroLocus_eq]
  exact Geometry.incidenceDimension_le_twelve ⟨_, hF.map _, hA⟩

theorem gradient_quotient_dimension_le_five
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ rationalGradientIdeal F) ≤ 5 := by
  rw [← RationalEquationDimension.rational_quotient_dimension_eq_geometric_zeroLocus
    _ (rationalGradientIdeal_ne_top F hF), gradient_zeroLocus_eq]
  exact Geometry.singularDimension_le_five ⟨_, hF.map _, hA⟩

end CubicTenVariables.CubicMassEquations
