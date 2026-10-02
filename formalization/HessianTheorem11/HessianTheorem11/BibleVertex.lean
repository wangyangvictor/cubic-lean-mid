import HessianTheorem11.PolarizationExpansion
import HessianTheorem11.GeometricInjectivity
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! The maximal affine vertex of a cubic, its actual translation
interpretation, and extension of the field of definition. -/

noncomputable section
namespace HessianTheorem11.BibleVertex
open MvPolynomial Module

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- The affine vertex is the kernel of the actual linear Hessian pencil. -/
def affineVertex (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) :
    Submodule K (Fin n → K) :=
  LinearMap.ker (hessianLinearMap F hF)

@[simp] theorem mem_affineVertex (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (v : Fin n → K) :
    v ∈ affineVertex F hF ↔ hessian F v = 0 := Iff.rfl

/-- This is an identity of evaluations on every translated line, not
only an assertion that the vertex lies on the cubic. -/
def TranslationDirection (F : MvPolynomial (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ x : Fin n → K, ∀ t : K, eval (x + t • v) F = eval x F

theorem translation_of_hessian_zero (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (v : Fin n → K) (hv : hessian F v = 0) :
    TranslationDirection F v := by
  intro x t
  have ht : hessian F (t • v) = 0 := by rw [hessian_smul hF, hv, smul_zero]
  have hp (a b : Fin n → K) : polarization F a b (t • v) = 0 := by
    simp [polarization, ht]
  have htv : eval (t • v) F = 0 := by
    rw [eval_cubic_eq_polarization hF, hp, mul_zero]
  rw [eval_cubic_add hF, htv, hp, hp]
  ring

theorem hessian_zero_of_translation (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (v : Fin n → K)
    (hv : TranslationDirection F v) : hessian F v = 0 := by
  have hzero : eval (0 : Fin n → K) F = 0 := by
    rw [eval_cubic_eq_polarization hF, polarization_zero_first, mul_zero]
  have hfv : eval v F = 0 := by
    have he := hv 0 1
    simpa only [one_smul, zero_add] using he.trans hzero
  have hquad (z : Fin n → K) : polarization F z z v = 0 := by
    have h₁ := eval_cubic_add hF z v
    have h₂ := eval_cubic_add hF ((-1 : K) • z) v
    have he₁ : eval (z + v) F = eval z F := by simpa using hv z 1
    have he₂ : eval ((-1 : K) • z + v) F = eval ((-1 : K) • z) F := by
      simpa using hv ((-1 : K) • z) 1
    rw [he₁, hfv] at h₁
    rw [he₂, hfv, polarization_smul_first, polarization_smul_second,
      polarization_smul_first] at h₂
    linear_combination -h₁ - h₂
  have hp (a b : Fin n → K) : polarization F a b v = 0 := by
    have hab := hquad (a+b)
    rw [polarization_add_first, polarization_add_second, polarization_add_second,
      hquad a, hquad b, polarization_swap_first F b a v] at hab
    linear_combination (1 / 2 : K) * hab
  ext i j
  have hij := hp (Pi.single i 1) (Pi.single j 1)
  simpa [polarization, Matrix.mulVec, dotProduct, Pi.single_apply] using hij

theorem mem_affineVertex_iff_translation (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (v : Fin n → K) :
    v ∈ affineVertex F hF ↔ TranslationDirection F v :=
  ⟨translation_of_hessian_zero F hF v, hessian_zero_of_translation F hF v⟩

theorem maximal_vertex (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (W : Submodule K (Fin n → K)) :
    W ≤ affineVertex F hF ↔ ∀ v ∈ W, TranslationDirection F v := by
  simp only [SetLike.le_def, mem_affineVertex_iff_translation]

/-- A homogeneous hypersurface is a projective cone precisely when its
affine equation has a nonzero direction of translation invariance.
The preceding theorem identifies its entire maximal vertex. -/
def IsProjectiveCone (F : MvPolynomial (Fin n) K) : Prop :=
  ∃ v : Fin n → K, v ≠ 0 ∧ TranslationDirection F v

theorem anisotropic_not_projectiveCone
    {L : Type*} [Field L] [CharZero L] [Algebra ℚ L] (F : AnisotropicCubic n) :
    ¬ IsProjectiveCone (map (algebraMap ℚ L) F.polynomial) := by
  rintro ⟨v, hv, htrans⟩
  exact hv ((baseChange_hessian_zero_iff F v).mp
    (hessian_zero_of_translation _ (F.homogeneous.map _) v htrans))

/-- Coefficient functionals commute with the Hessian pencil over any field. -/
theorem coefficient_hessian_entry
    {L : Type*} [Field L] [Algebra K L]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (φ : L →ₗ[K] K) (x : Fin n → L) (i j : Fin n) :
    φ (hessian (map (algebraMap K L) F) x i j) =
      hessian F (fun k => φ (x k)) i j := by
  rw [hessian_entry_expansion (hF.map _), hessian_entry_expansion hF]
  simp only [pderiv_map, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm, ← Algebra.smul_def, φ.map_smul]
  simp [smul_eq_mul, mul_comm]

/-- The maximal vertex over an extension is precisely the scalar span
of the vertex over the field of definition. This is actual kernel descent,
with no external descent assumption. -/
theorem affineVertex_baseChange
    {L : Type*} [Field L] [Algebra K L]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) :
    affineVertex (map (algebraMap K L) F) (hF.map _) =
      Submodule.span L ((fun v : Fin n → K => fun i => algebraMap K L (v i)) ''
        (affineVertex F hF : Set (Fin n → K))) := by
  classical
  let α := algebraMap K L
  let b := Basis.ofVectorSpace K L
  let ψ (i : Basis.ofVectorSpaceIndex K L) : L →ₗ[K] K :=
    (Finsupp.lapply i).comp b.repr.toLinearMap
  apply le_antisymm
  · intro x hx
    let v (i : Basis.ofVectorSpaceIndex K L) : Fin n → K := fun j => ψ i (x j)
    have hv (i) : v i ∈ affineVertex F hF := by
      change hessian F (v i) = 0
      ext j k
      rw [← coefficient_hessian_entry F hF (ψ i) x j k]
      change hessian (map α F) x = 0 at hx
      rw [hx]
      simp
    let S := Finset.univ.biUnion (fun j : Fin n => (b.repr (x j)).support)
    have hexp : x = ∑ i ∈ S, b i • (fun j => α (v i j)) := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hs : (b.repr (x j)).support ⊆ S := by
        intro i hi
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩
      have he := b.linearCombination_repr (x j)
      rw [Finsupp.linearCombination_apply, Finsupp.sum] at he
      calc
        x j = ∑ i ∈ (b.repr (x j)).support, b.repr (x j) i • b i := he.symm
        _ = ∑ i ∈ S, b.repr (x j) i • b i := by
          apply Finset.sum_subset hs
          intro i hi hn
          rw [Finsupp.notMem_support_iff.mp hn, zero_smul]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [v, ψ, α, Algebra.smul_def, mul_comm]
    rw [hexp]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨v i, hv i, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    change hessian F v = 0 at hv
    change hessian (map (algebraMap K L) F) (fun i => algebraMap K L (v i)) = 0
    ext i j
    have he : hessian (map (algebraMap K L) F)
        (fun i => algebraMap K L (v i)) i j = algebraMap K L (hessian F v i j) := by
      rw [hessian_entry_expansion (hF.map _), hessian_entry_expansion hF]
      simp only [pderiv_map, coeff_map, map_sum, map_mul]
    rw [he, hv]
    simp

end HessianTheorem11.BibleVertex
