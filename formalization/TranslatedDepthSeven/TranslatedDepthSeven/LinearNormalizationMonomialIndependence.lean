import TranslatedDepthSeven.AffinePlaneMonomialWeights
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Independent forms from a finite linear normalization

Let `B` be a polynomial subalgebra of a finite algebra `A`.  If `g_i` are
linearly independent over `B` and `m_u` are linearly independent over the
ground field in `B`, then the products `m_u g_i` are linearly independent
over the ground field in `A`.  This is the elementary independence argument
needed to turn a homogeneous linear normalization into the forms used in the
determinant matrix.

The final theorem applies this observation to the explicit degree-`k`
monomials in three normalization variables.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators
open MvPolynomial

universe u v w x y

/-- Multiplying the individual members of a linearly independent family by
nonzero scalars preserves independence over a domain.  No freeness or
torsion-freeness assumption on the ambient algebra is required. -/
theorem LinearIndependent.algebraMap_mul_of_ne_zero
    (B : Type v) (A : Type w)
    [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    (I : Type x) [Fintype I]
    (g : I → A) (hg : LinearIndependent B g)
    (s : I → B) (hs : ∀ i, s i ≠ 0) :
    LinearIndependent B
      (fun i ↦ algebraMap B A (s i) * g i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hrelation : ∑ j, (c j * s j) • g j = 0 := by
    simpa only [Algebra.smul_def, map_mul, mul_assoc] using hc
  have hzero : c i * s i = 0 :=
    Fintype.linearIndependent_iff.mp hg (fun j ↦ c j * s j) hrelation i
  exact (mul_eq_zero.mp hzero).resolve_right (hs i)

/-- Products of an independent family in the base algebra and an independent
family over that base algebra remain independent over the ground field. -/
theorem linearIndependent_algebraMap_mul
    (K : Type u) (B : Type v) (A : Type w)
    [Field K] [CommRing B] [CommRing A]
    [Algebra K B] [Algebra K A] [Algebra B A]
    [IsScalarTower K B A]
    (I : Type x) (U : Type y) [Fintype I] [Fintype U]
    (m : U → B) (g : I → A)
    (hm : LinearIndependent K m)
    (hg : LinearIndependent B g) :
    LinearIndependent K
      (fun p : I × U ↦ algebraMap B A (m p.2) * g p.1) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  let b : I → B := fun i ↦
    ∑ u, algebraMap K B (c (i, u)) * m u
  have hbg : ∑ i, b i • g i = 0 := by
    calc
      ∑ i, b i • g i =
          ∑ i, ∑ u,
            algebraMap K A (c (i, u)) *
              (algebraMap B A (m u) * g i) := by
        simp only [b, Algebra.smul_def, map_sum, map_mul,
          IsScalarTower.algebraMap_apply K B A, Finset.sum_mul]
        simp only [mul_assoc]
      _ = ∑ p : I × U,
          c p • (algebraMap B A (m p.2) * g p.1) := by
        rw [Fintype.sum_prod_type]
        simp only [Algebra.smul_def]
      _ = 0 := hc
  have hbzero : ∀ i, b i = 0 :=
    Fintype.linearIndependent_iff.mp hg b hbg
  have hmzero : ∑ u, c (p.1, u) • m u = 0 := by
    simpa only [b, Algebra.smul_def] using hbzero p.1
  exact Fintype.linearIndependent_iff.mp hm (fun u ↦ c (p.1, u)) hmzero p.2

/-- The exponent vectors indexing the full degree-`k` normalization block
are pairwise distinct. -/
theorem affinePlaneMonomialExponent_injective (k : ℕ) :
    Function.Injective (affinePlaneMonomialExponent k) := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  have h₁ : a.1 = a'.1 := by
    have := DFunLike.congr_fun h (1 : Fin 3)
    simpa [affinePlaneMonomialExponent] using this
  have h₂ : j.1 - a.1 = j'.1 - a'.1 := by
    have := DFunLike.congr_fun h (2 : Fin 3)
    simpa [affinePlaneMonomialExponent] using this
  have haj : a.1 ≤ j.1 := Nat.lt_succ_iff.mp a.2
  have haj' : a'.1 ≤ j'.1 := Nat.lt_succ_iff.mp a'.2
  have hj : j.1 = j'.1 := by omega
  have hj' : j = j' := Fin.ext hj
  subst j'
  have ha' : a = a' := Fin.ext h₁
  subst a'
  rfl

/-- The literal homogeneous monomials of degree `k` in three variables are
linearly independent. -/
theorem linearIndependent_affinePlaneHomogeneousMonomial
    (K : Type u) [Field K] (k : ℕ) :
    LinearIndependent K (affinePlaneHomogeneousMonomial K k) := by
  let e : AffinePlaneMonomialIndex k → (Fin 3 →₀ ℕ) :=
    affinePlaneMonomialExponent k
  have he : Function.Injective e := affinePlaneMonomialExponent_injective k
  have hmon : LinearIndependent K
      (fun d : Fin 3 →₀ ℕ ↦ MvPolynomial.monomial d (1 : K)) := by
    simpa only [MvPolynomial.coe_basisMonomials] using
      (MvPolynomial.basisMonomials (Fin 3) K).linearIndependent
  simpa only [affinePlaneHomogeneousMonomial, e] using hmon.comp e he

/-- A `B`-independent normalization basis, multiplied by the full explicit
degree-`k` monomial block in three variables, gives a ground-field independent
family in the finite algebra. -/
theorem linearIndependent_normalizationSurfaceBlock
    (K : Type u) (A : Type w)
    [Field K] [CommRing A]
    [Algebra K A] [Algebra (MvPolynomial (Fin 3) K) A]
    [IsScalarTower K (MvPolynomial (Fin 3) K) A]
    (I : Type x) [Fintype I]
    (g : I → A)
    (hg : LinearIndependent (MvPolynomial (Fin 3) K) g)
    (k : ℕ) :
    LinearIndependent K
      (fun p : I × AffinePlaneMonomialIndex k ↦
        algebraMap (MvPolynomial (Fin 3) K) A
            (affinePlaneHomogeneousMonomial K k p.2) * g p.1) := by
  exact linearIndependent_algebraMap_mul
    K (MvPolynomial (Fin 3) K) A I (AffinePlaneMonomialIndex k)
      (affinePlaneHomogeneousMonomial K k) g
      (linearIndependent_affinePlaneHomogeneousMonomial K k) hg

end

end TranslatedDepthSeven
