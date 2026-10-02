import CubicTenVariables.ReducedCubicVertex
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Scalar extension for the actual Hessian vertex. The proof is linear
algebra over arbitrary fields and imposes no characteristic-zero hypothesis. -/
noncomputable section
namespace CubicTenVariables.ReducedVertexBaseChange
open MvPolynomial HessianTheorem11 Module ReducedCubicVertex
variable {K : Type*} [Field K] {n : ℕ}

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

/-- The literal Hessian commutes with coefficient extension and with extension
of the evaluation point. -/
theorem hessian_map_point
    {L : Type*} [Field L] [Algebra K L]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (v : Fin n → K) :
    hessian (map (algebraMap K L) F) (fun i => algebraMap K L (v i)) =
      (hessian F v).map (algebraMap K L) := by
  ext i j
  change hessian (map (algebraMap K L) F) (fun k => algebraMap K L (v k)) i j =
    algebraMap K L (hessian F v i j)
  rw [hessian_entry_expansion (hF.map _), hessian_entry_expansion hF]
  simp only [pderiv_map, coeff_map, map_sum, map_mul]

/-- Triviality of the vertex can be checked over the field of definition. -/
theorem affineVertex_baseChange_eq_bot_iff
    {L : Type*} [Field L] [Algebra K L]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) :
    affineVertex (map (algebraMap K L) F) (hF.map _) = ⊥ ↔
      affineVertex F hF = ⊥ := by
  constructor
  · intro h
    apply bot_unique
    intro v hv
    change v=0
    have hv' : (fun i => algebraMap K L (v i)) ∈
        affineVertex (map (algebraMap K L) F) (hF.map _) := by
      change hessian _ _ = 0
      rw [hessian_map_point F hF v, (mem_affineVertex F hF v).mp hv]
      ext i j
      simp only [Matrix.map_apply, Matrix.zero_apply, map_zero]
    rw [h] at hv'
    have hz := (Submodule.mem_bot L).mp hv'
    ext i
    apply (algebraMap K L).injective
    simpa using congrFun hz i
  · intro h
    rw [affineVertex_baseChange F hF, h]
    apply bot_unique
    apply Submodule.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    have hv' : v=0 := (Submodule.mem_bot K).mp hv
    subst v
    exact show (fun i : Fin n => algebraMap K L (0 : K)) = 0 by ext i; simp

/-- Linear independence of a finite coordinate family is preserved by any
field extension. Coefficient functionals reduce a putative relation to the
original field. -/
theorem linearIndependent_map_coordinates
    {L : Type*} [Field L] [Algebra K L]
    {ι : Type*} [Fintype ι] (v : ι → Fin n → K)
    (hv : LinearIndependent K v) :
    LinearIndependent L (fun i j => algebraMap K L (v i j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let b := Basis.ofVectorSpace K L
  let ψ (a : Basis.ofVectorSpaceIndex K L) : L →ₗ[K] K :=
    (Finsupp.lapply a).comp b.repr.toLinearMap
  have hz (a : Basis.ofVectorSpaceIndex K L) (i : ι) : ψ a (c i)=0 := by
    apply (Fintype.linearIndependent_iff.mp hv) (fun i => ψ a (c i))
    ext j
    have he := congrArg (ψ a) (congrFun hc j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, Pi.zero_apply, map_zero] at he ⊢
    convert he using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm (c k), ← Algebra.smul_def, (ψ a).map_smul]
    simp [smul_eq_mul,mul_comm]
  intro i
  apply b.repr.injective
  ext a
  simpa [ψ] using hz a i

/-- The dimension of the vertex over its field of definition is at most its
geometric dimension. This applies to finite fields as well. -/
theorem affineVertex_finrank_le_baseChange
    {L : Type*} [Field L] [Algebra K L]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) :
    finrank K (affineVertex F hF) ≤
      finrank L (affineVertex (map (algebraMap K L) F) (hF.map _)) := by
  classical
  let V := affineVertex F hF
  let W := affineVertex (map (algebraMap K L) F) (hF.map _)
  let b := Module.finBasis K V
  let v (i : Fin (finrank K V)) : W :=
    ⟨fun j => algebraMap K L (((b i : V) : Fin n → K) j), by
      change hessian _ _ = 0
      rw [hessian_map_point F hF]
      have hb : hessian F (b i)=0 := (b i).property
      rw [hb]
      ext j k
      simp only [Matrix.map_apply, Matrix.zero_apply, map_zero]⟩
  have hb : LinearIndependent K (fun i => ((b i : V) : Fin n → K)) :=
    b.linearIndependent.map' V.subtype (by simp)
  have hv : LinearIndependent L v := by
    apply LinearIndependent.of_comp W.subtype
    exact linearIndependent_map_coordinates _ hb
  simpa only [Fintype.card_fin] using hv.fintype_card_le_finrank

/-- Any injective coordinate frame remains injective after field extension. -/
theorem map_frame_injective
    {L : Type*} [Field L] [Algebra K L] {m : ℕ}
    (B : Matrix (Fin n) (Fin m) K) (hB : Function.Injective B.mulVec) :
    Function.Injective (B.map (algebraMap K L)).mulVec := by
  apply Matrix.mulVec_injective_iff.mpr
  exact linearIndependent_map_coordinates B.col (Matrix.mulVec_injective_iff.mp hB)

end CubicTenVariables.ReducedVertexBaseChange
