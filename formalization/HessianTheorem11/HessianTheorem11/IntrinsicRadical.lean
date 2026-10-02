import HessianTheorem11.HessianLinearity
import HessianTheorem11.Polarization
import HessianTheorem11.AffineGeometry
import HessianTheorem11.Concentration

/-! The intrinsic radical of the first normal pairing, defined directly
from the actual Hessian kernels and cubic tensor. No local coordinates,
normal rank certificate, or incidence dimension is included in its definition. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- Those Hessian-kernel vectors whose polar matrix annihilates the entire
Hessian kernel. By cubic symmetry this is a linear subspace in v. -/
def intrinsicRadical (F : MvPolynomial (Fin n) K) (x : Fin n → K) :
    Submodule K (Fin n → K) :=
  LinearMap.ker (hessian F x).mulVecLin ⊓
    ⨅ u : LinearMap.ker (hessian F x).mulVecLin,
      LinearMap.ker (hessian F u).mulVecLin

theorem mem_intrinsicRadical_iff
    (F : MvPolynomial (Fin n) K) (x v : Fin n → K) :
    v ∈ intrinsicRadical F x ↔ (hessian F x).mulVec v = 0 ∧
      ∀ u, (hessian F x).mulVec u = 0 → (hessian F u).mulVec v = 0 := by
  simp only [intrinsicRadical, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, fun u hu => h ⟨u, hu⟩⟩
  · rintro ⟨hv, h⟩
    exact ⟨hv, fun u => h u u.property⟩

theorem intrinsicRadical_le_kernel (F : MvPolynomial (Fin n) K) (x : Fin n → K) :
    intrinsicRadical F x ≤ LinearMap.ker (hessian F x).mulVecLin := inf_le_left

theorem intrinsicRadical_annihilates_kernel
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    {x v : Fin n → K} (hv : v ∈ intrinsicRadical F x)
    {u : Fin n → K} (hu : u ∈ LinearMap.ker (hessian F x).mulVecLin) :
    (hessian F v).mulVec u = 0 := by
  rw [hessian_polarization hF]
  exact (mem_intrinsicRadical_iff F x v).mp hv |>.2 u hu

/-- Every intrinsic radical vector is genuinely singular on the cubic. -/
theorem intrinsicRadical_singular
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    {x v : Fin n → K} (hv : v ∈ intrinsicRadical F x) : gradient F v = 0 := by
  have hz := intrinsicRadical_annihilates_kernel hF hv (intrinsicRadical_le_kernel F x hv)
  rw [hessian_mulVec_self hF] at hz
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

theorem intrinsicRadical_radial_in_kernel
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    {x v : Fin n → K} (hv : v ∈ intrinsicRadical F x) :
    x ∈ LinearMap.ker (hessian F v).mulVecLin := by
  change (hessian F v).mulVec x = 0
  rw [hessian_polarization hF]
  exact intrinsicRadical_le_kernel F x hv

/-- The polar matrix at a radical vector kills both the original radial
line and the whole original Hessian kernel. -/
theorem intrinsicRadical_kernel_span
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    {x v : Fin n → K} (hv : v ∈ intrinsicRadical F x) :
    Submodule.span K {x} ⊔ LinearMap.ker (hessian F x).mulVecLin ≤
      LinearMap.ker (hessian F v).mulVecLin := by
  apply sup_le
  · apply Submodule.span_le.mpr
    intro z hz
    have he : z = x := Set.mem_singleton_iff.mp hz
    subst z
    exact intrinsicRadical_radial_in_kernel hF hv
  · intro u hu
    exact intrinsicRadical_annihilates_kernel hF hv hu

/-- The actual nonzero radical incidence above a chosen base open. -/
def radicalIncidence (F : GeometricPolynomial n) (O : Set (GeometricPoint n)) :
    Set ((Fin n ⊕ Fin n) → GeometricField) :=
  {p | p ∘ Sum.inl ∈ O ∧ p ∘ Sum.inr ≠ 0 ∧
    p ∘ Sum.inr ∈ intrinsicRadical F (p ∘ Sum.inl)}

theorem radicalIncidence_second_singular {F : GeometricPolynomial n}
    (hF : F.IsHomogeneous 3) (O : Set (GeometricPoint n))
    {p : (Fin n ⊕ Fin n) → GeometricField} (hp : p ∈ radicalIncidence F O) :
    gradient F (p ∘ Sum.inr) = 0 := intrinsicRadical_singular hF hp.2.2

/-- The full radical bundle includes the zero section. Its second image
is therefore a cone even when the chosen base open is not conical. -/
def radicalBundle (F : GeometricPolynomial n) (O : Set (GeometricPoint n)) :
    Set ((Fin n ⊕ Fin n) → GeometricField) :=
  {p | p ∘ Sum.inl ∈ O ∧ p ∘ Sum.inr ∈ intrinsicRadical F (p ∘ Sum.inl)}

def radicalImage (F : GeometricPolynomial n) (O : Set (GeometricPoint n)) :
    Set (GeometricPoint n) := (fun p => p ∘ Sum.inr) '' radicalBundle F O

theorem radicalImage_cone (F : GeometricPolynomial n) (O : Set (GeometricPoint n)) :
    IsAffineCone (radicalImage F O) := by
  intro a v hv
  obtain ⟨p, hp, rfl⟩ := hv
  refine ⟨Sum.elim (p ∘ Sum.inl) (a • (p ∘ Sum.inr)), ?_, rfl⟩
  change p ∘ Sum.inl ∈ O ∧ a • (p ∘ Sum.inr) ∈ intrinsicRadical F (p ∘ Sum.inl)
  exact ⟨hp.1, (intrinsicRadical F _).smul_mem a hp.2⟩

theorem IsAffineCone.geometricClosure {σ : Type*}
    {Z : Set (σ → GeometricField)} (hZ : IsAffineCone Z) :
    IsAffineCone (geometricClosure Z) := by
  intro a x hx
  let P : σ → MvPolynomial σ GeometricField := fun i => C a * X i
  have he (v : σ → GeometricField) : polynomialMap P v = a • v := by
    ext i
    simp [P, polynomialMap, Pi.smul_apply, smul_eq_mul]
  have hs : polynomialMap P '' Z ⊆ Z := by
    rintro _ ⟨v, hv, rfl⟩
    rw [he]
    exact hZ a v hv
  have hi := polynomialMap_image_closure_subset P Z ⟨x, hx, rfl⟩
  rw [he] at hi
  exact geometricClosure_mono hs hi

theorem radicalImage_closure_singular {F : GeometricPolynomial n}
    (hF : F.IsHomogeneous 3) (O : Set (GeometricPoint n)) :
    ∀ v ∈ geometricClosure (radicalImage F O), gradient F v = 0 := by
  intro v hv
  ext i
  apply geometricClosure_subset_of_polynomial_vanishes (radicalImage F O) (pderiv i F) _ v hv
  rintro w ⟨p, hp, rfl⟩
  exact congrFun (intrinsicRadical_singular hF hp.2) i

end HessianTheorem11
