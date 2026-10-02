import TranslatedDepthSeven.HomogeneousProjectiveTransport

/-!
# Concrete multivariate homogenization

This file homogenizes a multivariable polynomial by adjoining one variable,
indexed by `none`.  The old variables are indexed by `some i`.  At a target
degree `d`, the homogeneous component of degree `k` is multiplied by
`X none ^ (d-k)`.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped LinearAlgebra.Projectivization

open MvPolynomial Finset

universe u v

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- Multivariate homogenization at a prescribed target degree.  Terms of
degree greater than the target are discarded; when `totalDegree f ≤ d`, no
term is discarded. -/
def multivariateHomogenization (f : MvPolynomial σ R) (d : ℕ) :
    MvPolynomial (Option σ) R :=
  ∑ k ∈ range (d + 1),
    X none ^ (d - k) * rename some (homogeneousComponent k f)

/-- Substitution of `1` for the homogenizing coordinate and `X i` for the
coordinate `some i`. -/
def multivariateDehomogenization :
    MvPolynomial (Option σ) R →ₐ[R] MvPolynomial σ R :=
  aeval fun j ↦
    match j with
    | none => 1
    | some i => X i

@[simp]
theorem multivariateDehomogenization_X_none :
    multivariateDehomogenization (X (none : Option σ)) =
      (1 : MvPolynomial σ R) := by
  simp [multivariateDehomogenization]

@[simp]
theorem multivariateDehomogenization_rename
    (g : MvPolynomial σ R) :
    multivariateDehomogenization (rename some g) = g := by
  change aeval (fun j ↦ match j with | none => 1 | some i => X i)
      (rename some g) = g
  rw [aeval_rename]
  exact aeval_X_left_apply g

/-- A sum through degree `d` contains every homogeneous component when the
total degree is at most `d`. -/
theorem sum_homogeneousComponent_up_to
    (f : MvPolynomial σ R) (d : ℕ) (hfd : f.totalDegree ≤ d) :
    (∑ k ∈ range (d + 1), homogeneousComponent k f) = f := by
  calc
    (∑ k ∈ range (d + 1), homogeneousComponent k f) =
        ∑ k ∈ range (f.totalDegree + 1), homogeneousComponent k f := by
          symm
          apply sum_subset
          · intro k hk
            simp only [mem_range] at hk ⊢
            omega
          · intro k hk hkn
            apply homogeneousComponent_eq_zero
            simp only [mem_range] at hk hkn
            omega
    _ = f := f.sum_homogeneousComponent

/-- Dehomogenizing the concrete homogenization recovers the original
polynomial, provided the target degree is large enough. -/
theorem multivariateDehomogenization_homogenization
    (f : MvPolynomial σ R) (d : ℕ) (hfd : f.totalDegree ≤ d) :
    multivariateDehomogenization (multivariateHomogenization f d) = f := by
  rw [multivariateHomogenization]
  simp only [map_sum, map_mul, map_pow,
    multivariateDehomogenization_X_none,
    multivariateDehomogenization_rename, one_pow, one_mul]
  rw [sum_homogeneousComponent_up_to f d hfd]

/-- The concrete homogenization is homogeneous of its target degree. -/
theorem multivariateHomogenization_isHomogeneous
    (f : MvPolynomial σ R) (d : ℕ) :
    (multivariateHomogenization f d).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro k hk
  simp only [mem_range] at hk
  have hk_le : k ≤ d := Nat.le_of_lt_succ (by simpa only [Nat.add_eq, Nat.lt_add_one_iff] using hk)
  have hpow : (X (none : Option σ) ^ (d - k) : MvPolynomial (Option σ) R).IsHomogeneous
      (d - k) := isHomogeneous_X_pow none (d - k)
  have hcomponent :
      (rename some (homogeneousComponent k f) : MvPolynomial (Option σ) R).IsHomogeneous k :=
    (homogeneousComponent_isHomogeneous k f).rename_isHomogeneous
  simpa [Nat.sub_add_cancel hk_le] using hpow.mul hcomponent

variable {K : Type u} [Field K]

/-- Evaluating a dehomogenized polynomial at `z` is the same as evaluating
the original homogeneous-coordinate polynomial at `(1,z)`. -/
theorem eval_multivariateDehomogenization
    (g : MvPolynomial (Option σ) K) (z : σ → K) :
    eval z (multivariateDehomogenization g) = eval (affineChartVector z) g := by
  let lhs : MvPolynomial (Option σ) K →+* K :=
    (eval z).comp multivariateDehomogenization.toRingHom
  let rhs : MvPolynomial (Option σ) K →+* K :=
    eval (affineChartVector z)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, rhs, multivariateDehomogenization]
    · intro j
      cases j <;> simp [lhs, rhs, multivariateDehomogenization,
        affineChartVector]
  exact RingHom.congr_fun hhom g

/-- Evaluation of the homogenization on the standard affine representative
`[1:z]` recovers evaluation of the original polynomial. -/
theorem eval_affineChartVector_multivariateHomogenization
    (f : MvPolynomial σ K) (d : ℕ) (hfd : f.totalDegree ≤ d)
    (z : σ → K) :
    eval (affineChartVector z) (multivariateHomogenization f d) = eval z f := by
  calc
    eval (affineChartVector z) (multivariateHomogenization f d) =
        eval z (multivariateDehomogenization
          (multivariateHomogenization f d)) :=
      (eval_multivariateDehomogenization _ z).symm
    _ = eval z f := by
      rw [multivariateDehomogenization_homogenization f d hfd]

/-- On the standard affine chart, the projective hypersurface of the
homogenization cuts out exactly the original affine hypersurface. -/
theorem affineChartPoint_mem_homogeneousProjectiveHypersurface_homogenization_iff
    (f : MvPolynomial σ K) (d : ℕ) (hfd : f.totalDegree ≤ d)
    (z : σ → K) :
    affineChartPoint z ∈
        homogeneousProjectiveHypersurface (multivariateHomogenization f d) ↔
      eval z f = 0 := by
  rw [affineChartPoint]
  rw [mk_mem_homogeneousProjectiveHypersurface_iff _ d
    (multivariateHomogenization_isHomogeneous f d)]
  change eval (affineChartVector z) (multivariateHomogenization f d) = 0 ↔ _
  rw [eval_affineChartVector_multivariateHomogenization f d hfd z]

end

end TranslatedDepthSeven
