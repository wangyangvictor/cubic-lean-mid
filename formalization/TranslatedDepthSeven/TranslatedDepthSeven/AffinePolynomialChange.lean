import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Affine changes of variables in a polynomial ring

This file records the literal affine substitution used before applying a
point-counting theorem.  It contains no geometric or counting hypothesis.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

variable {R σ : Type*} [Field R]

/-- Substitution `X i ↦ y₀ i + r * X i`. -/
def affinePolynomialChangeHom (y₀ : σ → R) (r : R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i ↦ C (y₀ i) + C r * X i

/-- The inverse substitution, provided `r ≠ 0`. -/
def affinePolynomialChangeInvHom (y₀ : σ → R) (r : R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i ↦ C r⁻¹ * (X i - C (y₀ i))

@[simp] theorem affinePolynomialChangeHom_X (y₀ : σ → R) (r : R) (i : σ) :
    affinePolynomialChangeHom y₀ r (X i) = C (y₀ i) + C r * X i := by
  simp [affinePolynomialChangeHom]

@[simp] theorem affinePolynomialChangeInvHom_X (y₀ : σ → R) (r : R) (i : σ) :
    affinePolynomialChangeInvHom y₀ r (X i) = C r⁻¹ * (X i - C (y₀ i)) := by
  simp [affinePolynomialChangeInvHom]

/-- The affine substitution is an algebra automorphism when its scalar is
nonzero. -/
def affinePolynomialChangeAlgEquiv (y₀ : σ → R) (r : R) (hr : r ≠ 0) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (affinePolynomialChangeHom y₀ r)
    (affinePolynomialChangeInvHom y₀ r)
    (by
      ext i
      simp [affinePolynomialChangeHom, affinePolynomialChangeInvHom, hr])
    (by
      ext i
      simp [affinePolynomialChangeHom, affinePolynomialChangeInvHom, hr])

@[simp] theorem affinePolynomialChangeAlgEquiv_X
    (y₀ : σ → R) (r : R) (hr : r ≠ 0) (i : σ) :
    affinePolynomialChangeAlgEquiv y₀ r hr (X i) = C (y₀ i) + C r * X i := by
  simp [affinePolynomialChangeAlgEquiv]

/-- Evaluation after the affine substitution is evaluation at the affine
translate of the point. -/
theorem aeval_affinePolynomialChange (y₀ z : σ → R) (r : R) (hr : r ≠ 0)
    (f : MvPolynomial σ R) :
    aeval z (affinePolynomialChangeAlgEquiv y₀ r hr f) =
      aeval (fun i ↦ y₀ i + r * z i) f := by
  change (aeval z).comp (affinePolynomialChangeHom y₀ r) f = _
  congr 1
  ext i
  simp [affinePolynomialChangeHom]

/-- Evaluation after the inverse substitution. -/
theorem aeval_affinePolynomialChange_symm (y₀ z : σ → R) (r : R) (hr : r ≠ 0)
    (f : MvPolynomial σ R) :
    aeval z ((affinePolynomialChangeAlgEquiv y₀ r hr).symm f) =
      aeval (fun i ↦ r⁻¹ * (z i - y₀ i)) f := by
  change (aeval z).comp (affinePolynomialChangeInvHom y₀ r) f = _
  congr 1
  ext i
  simp [affinePolynomialChangeInvHom]

/-- Substitution of affine-linear polynomials cannot increase total degree. -/
theorem totalDegree_aeval_le_of_totalDegree_le_one
    {S τ : Type*} [CommSemiring S] (g : σ → MvPolynomial τ S)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (f : MvPolynomial σ S) :
    (aeval g f).totalDegree ≤ f.totalDegree := by
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  change (C (coeff d f)).totalDegree + (d.prod fun i k ↦ g i ^ k).totalDegree ≤ _
  rw [totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finset_prod d.support fun i ↦ g i ^ d i).trans ?_
  calc
    ∑ i ∈ d.support, (g i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (totalDegree_pow (g i) (d i)).trans
        (by simpa using Nat.mul_le_mul_left (d i) (hg i))
    _ = d.sum fun _ e ↦ e := by simp [Finsupp.sum]
    _ ≤ f.totalDegree := le_totalDegree hd

/-- An invertible affine change preserves total degree exactly. -/
theorem totalDegree_affinePolynomialChange (y₀ : σ → R) (r : R) (hr : r ≠ 0)
    (f : MvPolynomial σ R) :
    (affinePolynomialChangeAlgEquiv y₀ r hr f).totalDegree = f.totalDegree := by
  apply le_antisymm
  · apply totalDegree_aeval_le_of_totalDegree_le_one
    intro i
    refine (totalDegree_add _ _).trans ?_
    refine max_le (by simp) ?_
    exact (totalDegree_mul _ _).trans (by simp)
  · have h := totalDegree_aeval_le_of_totalDegree_le_one
        (fun i ↦ C r⁻¹ * (X i - C (y₀ i)))
        (fun i ↦ by
          refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_C, zero_add]
          exact (totalDegree_sub _ _).trans (by simp))
        (affinePolynomialChangeAlgEquiv y₀ r hr f)
    change ((affinePolynomialChangeAlgEquiv y₀ r hr).symm
      (affinePolynomialChangeAlgEquiv y₀ r hr f)).totalDegree ≤ _ at h
    simpa using h

/-- Mapping an ideal and then pulling it back along the same affine
automorphism recovers the ideal exactly. -/
theorem affinePolynomialChange_comap_map (y₀ : σ → R) (r : R) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial σ R)) :
    (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)).comap
        (affinePolynomialChangeAlgEquiv y₀ r hr) = I :=
  Ideal.comap_map_of_bijective _ (affinePolynomialChangeAlgEquiv y₀ r hr).bijective

/-- An affine automorphism carries a prime ideal to a prime ideal. -/
theorem affinePolynomialChange_map_isPrime (y₀ : σ → R) (r : R) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial σ R)) [I.IsPrime] :
    (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)).IsPrime := by
  infer_instance

/-- The induced equivalence of quotient algebras. -/
def affinePolynomialChangeQuotientAlgEquiv (y₀ : σ → R) (r : R) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial σ R)) :
    (MvPolynomial σ R ⧸ I) ≃ₐ[R]
      MvPolynomial σ R ⧸ I.map (affinePolynomialChangeAlgEquiv y₀ r hr) :=
  Ideal.quotientEquivAlg I _ (affinePolynomialChangeAlgEquiv y₀ r hr) rfl

/-- Consequently the source and transformed quotient rings have equal Krull
dimension. -/
theorem affinePolynomialChange_quotient_ringKrullDim_eq
    (y₀ : σ → R) (r : R) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial σ R)) :
    ringKrullDim (MvPolynomial σ R ⧸ I) =
      ringKrullDim (MvPolynomial σ R ⧸
        I.map (affinePolynomialChangeAlgEquiv y₀ r hr)) :=
  ringKrullDim_eq_of_ringEquiv
    (affinePolynomialChangeQuotientAlgEquiv y₀ r hr I).toRingEquiv

end

end TranslatedDepthSeven
