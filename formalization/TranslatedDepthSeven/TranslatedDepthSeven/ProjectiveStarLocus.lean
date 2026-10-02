import TranslatedDepthSeven.EquationFamilyProjectiveTangentSpace
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The projective star cut out by the explicit line equations

For a finite family of homogeneous integral equations and an integral base
point `h`, this file packages the coefficient equations of
`f(h + T z)` into one finite homogeneous family.  It proves that their
projective common zero locus is exactly the set of directions `z` for which
the complete rational line through `h` in direction `z` lies on every
original equation.

This is an equation-level construction of the projective star.  It makes no
claim about irreducible components or the dimension of that star.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped LinearAlgebra.Projectivization

open Finset MvPolynomial Polynomial

/-- The finite family consisting of every coefficient of `f(h + T z)` from
order zero through the prescribed homogeneous degree of `f`. -/
def projectiveStarEquationFamily {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (degree : MvPolynomial (Fin n) ℤ → ℕ) (h : IntVector n) :
    Finset (MvPolynomial (Fin n) ℤ) :=
  equations.biUnion fun f ↦
    (Finset.range (degree f + 1)).image (starCoefficient f h)

/-- Every displayed projective-star equation is homogeneous, with degree its
coefficient index. -/
theorem mem_projectiveStarEquationFamily_isHomogeneous {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (degree : MvPolynomial (Fin n) ℤ → ℕ) (h : IntVector n)
    {g : MvPolynomial (Fin n) ℤ}
    (hg : g ∈ projectiveStarEquationFamily equations degree h) :
    ∃ k : ℕ, g.IsHomogeneous k := by
  classical
  simp only [projectiveStarEquationFamily, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_range] at hg
  obtain ⟨f, _hf, k, _hk, rfl⟩ := hg
  exact ⟨k, starCoefficient_isHomogeneous f h k⟩

/-- The rational polynomial obtained by restricting the coefficient-extended
equation `f` to the rational line `h + T z`. -/
def rationalLinePolynomial {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (h : IntVector n) (z : Fin n → ℚ) :
    Polynomial ℚ :=
  (symbolicLinePolynomial f h).map
    (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) z)

/-- Coefficients of the rational line restriction are evaluations of the
coefficient-extended star equations. -/
theorem coeff_rationalLinePolynomial {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (h : IntVector n) (z : Fin n → ℚ)
    (k : ℕ) :
    (rationalLinePolynomial f h z).coeff k =
      MvPolynomial.eval z
        (MvPolynomial.map (Int.castRingHom ℚ) (starCoefficient f h k)) := by
  simp [rationalLinePolynomial, starCoefficient,
    MvPolynomial.eval_map]

/-- Evaluation of the rational line restriction at `t` is literal
substitution of `h + t z` into the coefficient-extended equation. -/
theorem eval_rationalLinePolynomial {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (h : IntVector n) (z : Fin n → ℚ)
    (t : ℚ) :
    (rationalLinePolynomial f h z).eval t =
      MvPolynomial.eval (fun i ↦ (h i : ℚ) + t * z i)
        (MvPolynomial.map (Int.castRingHom ℚ) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rationalLinePolynomial, symbolicLinePolynomial]
  | add f g hf hg =>
      rw [rationalLinePolynomial, symbolicLinePolynomial_add,
        Polynomial.map_add, Polynomial.eval_add]
      rw [show Polynomial.map (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) z)
          (symbolicLinePolynomial f h) = rationalLinePolynomial f h z by rfl,
        show Polynomial.map (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) z)
          (symbolicLinePolynomial g h) = rationalLinePolynomial g h z by rfl,
        hf, hg]
      simp
  | mul_X f i hf =>
      have hx :
          Polynomial.eval t
              (Polynomial.map
                (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) z)
                (symbolicLinePolynomial (MvPolynomial.X i) h)) =
            MvPolynomial.eval (fun j ↦ (h j : ℚ) + t * z j)
              (MvPolynomial.map (Int.castRingHom ℚ)
                (MvPolynomial.X i)) := by
        simp [symbolicLinePolynomial_X]
        ring
      rw [rationalLinePolynomial, symbolicLinePolynomial_mul,
        Polynomial.map_mul, Polynomial.eval_mul]
      rw [map_mul, MvPolynomial.eval_mul]
      exact congrArg₂ (· * ·) hf hx

/-- The first rational star coefficient is the Jacobian row paired with the
direction vector.  This is the coefficient-extended form of the usual first
polar identity. -/
theorem eval_map_starCoefficient_one_eq_rationalDirectionalDerivative
    {n : ℕ} (f : MvPolynomial (Fin n) ℤ) (h : IntVector n)
    (z : Fin n → ℚ) :
    MvPolynomial.eval z
        (MvPolynomial.map (Int.castRingHom ℚ) (starCoefficient f h 1)) =
      ∑ i, (MvPolynomial.eval h (MvPolynomial.pderiv i f) : ℚ) * z i := by
  have hpoly : starCoefficient f h 1 =
      ∑ i, MvPolynomial.C (MvPolynomial.eval h (MvPolynomial.pderiv i f)) *
        MvPolynomial.X i := by
    apply MvPolynomial.funext
    intro w
    rw [eval_starCoefficient_one_eq_directionalDerivative]
    simp
  rw [hpoly]
  simp

/-- For a homogeneous equation of the prescribed degree, vanishing of the
finitely many star equations is equivalent to vanishing at every rational
point of the corresponding affine line. -/
theorem starCoefficients_upto_degree_iff_rational_line {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (d : ℕ) (h : IntVector n)
    (z : Fin n → ℚ) (hf : f.IsHomogeneous d) :
    (∀ k < d + 1,
        MvPolynomial.eval z
          (MvPolynomial.map (Int.castRingHom ℚ) (starCoefficient f h k)) = 0) ↔
      ∀ t : ℚ,
        MvPolynomial.eval (fun i ↦ (h i : ℚ) + t * z i)
          (MvPolynomial.map (Int.castRingHom ℚ) f) = 0 := by
  have hdegree : f.totalDegree ≤ d := hf.totalDegree_le
  constructor
  · intro hcoeff t
    rw [← eval_rationalLinePolynomial f h z t]
    have hpoly : rationalLinePolynomial f h z = 0 := by
      apply Polynomial.ext
      intro k
      rw [coeff_rationalLinePolynomial]
      by_cases hk : k < d + 1
      · exact hcoeff k hk
      · have hdk : d < k := by omega
        have hzero : starCoefficient f h k = 0 :=
          starCoefficient_eq_zero_of_totalDegree_lt f h
            (lt_of_le_of_lt hdegree hdk)
        simp [hzero]
    rw [hpoly]
    simp
  · intro hline k _hk
    rw [← coeff_rationalLinePolynomial]
    have hzero : rationalLinePolynomial f h z = 0 :=
      Polynomial.zero_of_eval_zero _ fun t ↦ by
        rw [eval_rationalLinePolynomial]
        exact hline t
    rw [hzero]
    simp

/-- The projective star is the literal projectivized common zero locus of the
finite coefficient family. -/
def integralProjectiveStarLocus {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (degree : MvPolynomial (Fin n) ℤ → ℕ) (h : IntVector n) :
    Set (ℙ ℚ (Fin n → ℚ)) :=
  integralProjectiveConeZeroSetOver ℚ
    (projectiveStarEquationFamily equations degree h)

/-- A nonzero rational direction belongs to the displayed projective star if
and only if the entire rational affine line through `h` in that direction
lies on every original equation. -/
theorem mk_mem_integralProjectiveStarLocus_iff {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (degree : MvPolynomial (Fin n) ℤ → ℕ) (h : IntVector n)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (z : Fin n → ℚ) (hz : z ≠ 0) :
    Projectivization.mk ℚ z hz ∈
        integralProjectiveStarLocus equations degree h ↔
      ∀ f ∈ equations, ∀ t : ℚ,
        MvPolynomial.eval (fun i ↦ (h i : ℚ) + t * z i)
          (MvPolynomial.map (Int.castRingHom ℚ) f) = 0 := by
  classical
  let starDegree : MvPolynomial (Fin n) ℤ → ℕ := fun g ↦
    if hg : ∃ k, g.IsHomogeneous k then Classical.choose hg else 0
  have hstarHom : ∀ g ∈ projectiveStarEquationFamily equations degree h,
      g.IsHomogeneous (starDegree g) := by
    intro g hg
    have hex := mem_projectiveStarEquationFamily_isHomogeneous
      equations degree h hg
    simp only [starDegree, dif_pos hex]
    exact Classical.choose_spec hex
  rw [integralProjectiveStarLocus,
    mk_mem_integralProjectiveConeZeroSetOver_iff
      (projectiveStarEquationFamily equations degree h) starDegree hstarHom z hz]
  simp only [mem_integralAffineConeZeroSetOver_iff,
    projectiveStarEquationFamily, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_range]
  constructor
  · intro hstar f hf
    apply (starCoefficients_upto_degree_iff_rational_line
      f (degree f) h z (hhom f hf)).1
    intro k hk
    exact hstar (starCoefficient f h k) ⟨f, hf, k, hk, rfl⟩
  · intro hline g hg
    obtain ⟨f, hf, k, hk, rfl⟩ := hg
    exact (starCoefficients_upto_degree_iff_rational_line
      f (degree f) h z (hhom f hf)).2 (hline f hf) k hk

/-- Thus the equation-level projective star is contained in both the original
projective cone and the displayed projective tangent space. -/
theorem integralProjectiveStarLocus_subset_cone_inter_tangent {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (degree : MvPolynomial (Fin n) ℤ → ℕ) (h : IntVector n)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f)) :
    integralProjectiveStarLocus equations degree h ⊆
      integralProjectiveConeZeroSetOver ℚ equations ∩
        equationFamilyRationalProjectiveTangentSpace equations h := by
  intro P hP
  rw [Set.mem_inter_iff]
  let z : Fin n → ℚ := P.rep
  have hz : z ≠ 0 := P.rep_nonzero
  have hPmk : Projectivization.mk ℚ z hz = P := Projectivization.mk_rep P
  have hline : ∀ f ∈ equations, ∀ t : ℚ,
      MvPolynomial.eval (fun i ↦ (h i : ℚ) + t * z i)
        (MvPolynomial.map (Int.castRingHom ℚ) f) = 0 :=
    (mk_mem_integralProjectiveStarLocus_iff
      equations degree h hhom z hz).1 (hPmk.symm ▸ hP)
  constructor
  · rw [← hPmk, mk_mem_integralProjectiveConeZeroSetOver_iff
      equations degree hhom z hz]
    intro f hf
    have hpoly : rationalLinePolynomial f h z = 0 :=
      Polynomial.zero_of_eval_zero _ fun t ↦ by
        rw [eval_rationalLinePolynomial]
        exact hline f hf t
    have hlead := congrArg (fun q : Polynomial ℚ ↦ q.coeff (degree f)) hpoly
    change (rationalLinePolynomial f h z).coeff (degree f) = 0 at hlead
    rw [coeff_rationalLinePolynomial,
      starCoefficient_eq_of_isHomogeneous f h (degree f) (hhom f hf)] at hlead
    exact hlead
  · rw [← hPmk]
    change z ∈ equationFamilyRationalTangentKernel equations h
    rw [equationFamilyRationalTangentKernel, LinearMap.mem_ker]
    funext f
    change ∑ i,
      (MvPolynomial.eval h (MvPolynomial.pderiv i f.1) : ℚ) * z i = 0
    have hlinef := hline f.1 f.2
    have hpoly : rationalLinePolynomial f.1 h z = 0 :=
      Polynomial.zero_of_eval_zero _ fun t ↦ by
        rw [eval_rationalLinePolynomial]
        exact hlinef t
    have hcoeff1 := congrArg (fun q : Polynomial ℚ ↦ q.coeff 1) hpoly
    change (rationalLinePolynomial f.1 h z).coeff 1 = 0 at hcoeff1
    rw [coeff_rationalLinePolynomial] at hcoeff1
    rw [eval_map_starCoefficient_one_eq_rationalDirectionalDerivative]
      at hcoeff1
    exact hcoeff1

end

end TranslatedDepthSeven
