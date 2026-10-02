import HessianTheorem11.LinearArcSchur
import HessianTheorem11.SaturatedCubicResolvent

/-! The mixed tangent coefficient of the actual cubic Schur complement.
This proves the local-geometric part of source Lemma 34.4 from the
universal smooth-arc input, retaining all complementary block variations. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

def polarizationBlockLinear {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) {ι τ : Type*}
    (u : ι → GeometricPoint n) (v : τ → GeometricPoint n) :
    GeometricPoint n →ₗ[GeometricField] Matrix ι τ GeometricField where
  toFun y := fun i j => polarization F (u i) (v j) y
  map_add' y z := by ext i j; exact polarization_add_third hF _ _ _ _
  map_smul' c y := by ext i j; exact polarization_smul_third hF _ _ _ _

namespace CoisotropicBasis.Data
variable {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d q)

def radicalGramAt (y : GeometricPoint n) : Matrix (Fin m) (Fin m) GeometricField :=
  fun i j => polarization F (D.radicalVector i) (D.radicalVector j) y

def fullCrossAt (y : GeometricPoint n) :
    Matrix (Fin m) (CoisotropicBasis.NondegenerateIndex d q) GeometricField :=
  fun i j => polarization F (D.radicalVector i) (D.complementVector j) y

theorem full_gramAt (y : GeometricPoint n) :
    fromBlocks (D.radicalGramAt y) (D.fullCrossAt y) (D.fullCrossAt y).transpose
      (D.complementGramAt y) = D.gramAt y := by
  ext i j
  cases i <;> cases j
  · rfl
  · rfl
  · exact polarization_swap_first F _ _ y
  · rfl

theorem fullCrossAt_base : D.fullCrossAt x = 0 := by
  ext i j
  exact congrFun (congrFun D.gramAt_base (Sum.inl i)) (Sum.inr j)

theorem complementGramAt_base_inverse : (D.complementGramAt x)⁻¹ =
    SaturatedResolvent.initial (β := Fin d) D.middleGram⁻¹ := by
  rw [D.complementGramAt_base]
  apply Matrix.inv_eq_right_inv
  exact SaturatedResolvent.initial_mul D.middleGram D.middleGram⁻¹
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr D.middleGram_det_ne_zero))

theorem complementGramAt_base_det_ne_zero : (D.complementGramAt x).det ≠ 0 := by
  rw [D.complementGramAt_base]
  exact isUnit_iff_ne_zero.mp
    (SaturatedResolvent.initial_isUnit_det D.middleGram D.middleGram_det_ne_zero)

theorem mixed_fullCross_mem_radicalGram_range (SA : FormalSmoothArcInput)
    (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hx : x ∈ Z)
    (hT : T = affineTangentSpace Z x)
    (hdim : affineDimension Z = (finrank GeometricField T : Dimension))
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (a b : GeometricPoint n) (ha : a ∈ T) (hb : b ∈ T) :
    D.fullCrossAt a * (D.complementGramAt x)⁻¹ * (D.fullCrossAt b).transpose +
      D.fullCrossAt b * (D.complementGramAt x)⁻¹ * (D.fullCrossAt a).transpose ∈
        LinearMap.range (polarizationBlockLinear F hF D.radicalVector D.radicalVector) := by
  apply LinearArcSchur.mixed_schur_mem_range SA Z hZ hirred x hx
    (by rw [hT] at hdim; exact hdim)
    (polarizationBlockLinear F hF D.radicalVector D.radicalVector)
    (polarizationBlockLinear F hF D.radicalVector D.complementVector)
    (polarizationBlockLinear F hF D.complementVector D.complementVector)
  · intro y hy
    change (fromBlocks (D.radicalGramAt y) (D.fullCrossAt y) (D.fullCrossAt y).transpose
      (D.complementGramAt y)).rank ≤ Fintype.card (CoisotropicBasis.NondegenerateIndex d q)
    rw [D.full_gramAt, D.gramAt_rank]
    have hr := hmax y hy
    have hd := D.hessian_dimensions.2
    simp only [CoisotropicBasis.NondegenerateIndex,Fintype.card_sum,Fintype.card_fin]
    omega
  · exact D.fullCrossAt_base
  · exact D.complementGramAt_base_det_ne_zero
  · rwa [← hT]
  · rwa [← hT]

theorem fullCrossAt_radical (hF : F.IsHomogeneous 3)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (a : GeometricPoint n) (ha : a ∈ LinearMap.ker (hessian F x).mulVecLin) :
    D.fullCrossAt a = SaturatedResolvent.cross (α := Fin q) (D.normalCross a) := by
  ext i j
  rcases j with j | (j | j)
  · exact D.cross_radical_tangent_zero hF hann a ha i _ (D.tangent_middle j)
  · exact D.cross_radical_tangent_zero hF hann a ha i _ (D.tangent_isotropic j)
  · rfl

/-- Multiplication by the inverse hyperbolic Gram matrix retains exactly
the isotropic columns of the other factor. All its middle and dual
columns are arbitrary in this identity. -/
theorem cross_initial_product {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] (P : Matrix γ β GeometricField)
    (B : Matrix α α GeometricField) (C : Matrix γ (α ⊕ (β ⊕ β)) GeometricField) :
    SaturatedResolvent.cross (α := α) P * SaturatedResolvent.initial B * C.transpose =
      P * (C.submatrix id (fun j => Sum.inr (Sum.inl j))).transpose := by
  ext i j
  simp [SaturatedResolvent.cross,SaturatedResolvent.initial,Matrix.mul_apply,
    Fintype.sum_sum_type,Matrix.one_apply]

theorem radicalGram_range_finrank_le
    (hF : F.IsHomogeneous 3)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0) :
    finrank GeometricField (LinearMap.range
      (polarizationBlockLinear F hF D.radicalVector D.radicalVector)) ≤ d := by
  let A := polarizationBlockLinear F hF D.radicalVector D.radicalVector
  have hle : T ≤ LinearMap.ker A := by
    intro t ht
    ext i j
    change polarization F (D.radicalVector i) (D.radicalVector j) t = 0
    rw [polarization_rotate hF]
    exact hann t ht _ (D.radical_hessian_kernel i) _ (D.radical_hessian_kernel j)
  have hk := Submodule.finrank_mono hle
  have hr := A.finrank_range_add_finrank_ker
  have hc := D.codimension
  simp only [Module.finrank_pi,Fintype.card_fin,Module.finrank_self,mul_one] at hr hc
  change d + finrank GeometricField T = n at hc
  change finrank GeometricField T ≤ finrank GeometricField (LinearMap.ker A) at hk
  change finrank GeometricField (LinearMap.range A) ≤ d
  omega

theorem fullCrossAt_radial_column_zero (hF : F.IsHomogeneous 3)
    (b : GeometricPoint n) (i : Fin m) :
    D.fullCrossAt b i (Sum.inr (Sum.inl D.radial)) = 0 := by
  change polarization F (D.radicalVector i)
    (D.basis (Sum.inr (Sum.inr (Sum.inl D.radial)))) b = 0
  rw [D.radial_eq,polarization_swap_last hF,polarization_swap_first]
  change dotProduct b ((hessian F x).mulVec (D.radicalVector i)) = 0
  rw [show (hessian F x).mulVec (D.radicalVector i) = 0 from D.radical_hessian_kernel i]
  simp

end CoisotropicBasis.Data

namespace CoisotropicBasis.Data
variable {n m q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m 2 q)

/-- The actual mixed product of the nonradial normal column and the
nonradial isotropic covector belongs to the actual normal pencil. -/
theorem two_normal_mixed_identity (SA : FormalSmoothArcInput)
    (hF : F.IsHomogeneous 3)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hx : x ∈ Z)
    (hT : T = affineTangentSpace Z x)
    (hdim : affineDimension Z = (finrank GeometricField T : Dimension))
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (η : Fin 2) (hη : η ≠ D.radial)
    (a b : GeometricPoint n) (ha : a ∈ LinearMap.ker (hessian F x).mulVecLin)
    (hb : b ∈ T) :
    (fun i j => D.normalCross a i η *
      polarization F (D.radicalVector j) (D.isotropicVector η) b +
      polarization F (D.radicalVector i) (D.isotropicVector η) b *
        D.normalCross a j η) ∈ LinearMap.range
      (polarizationBlockLinear F hF D.radicalVector D.radicalVector) := by
  have hfirst : D.fullCrossAt a * (D.complementGramAt x)⁻¹ * (D.fullCrossAt b).transpose =
      fun i j => D.normalCross a i η *
        polarization F (D.radicalVector j) (D.isotropicVector η) b := by
    rw [D.fullCrossAt_radical hF hann a ha,D.complementGramAt_base_inverse,
      cross_initial_product]
    ext i j
    change (∑ k, D.normalCross a i k *
      D.fullCrossAt b j (Sum.inr (Sum.inl k))) = _
    rw [Finset.sum_eq_single η]
    · rfl
    · intro k _ hk
      have hkr : k = D.radial := by
        apply Fin.ext
        have hkη : k.val ≠ η.val := fun h => hk (Fin.ext h)
        have hηr : η.val ≠ D.radial.val := fun h => hη (Fin.ext h)
        have hklt := k.isLt
        have hηlt := η.isLt
        have hrlt := D.radial.isLt
        omega
      rw [hkr,D.fullCrossAt_radial_column_zero hF,mul_zero]
    · simp
  have hsym : ((D.complementGramAt x)⁻¹).transpose = (D.complementGramAt x)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv,D.complementGramAt_symmetric x]
  have hsecond : D.fullCrossAt b * (D.complementGramAt x)⁻¹ * (D.fullCrossAt a).transpose =
      fun i j => polarization F (D.radicalVector i) (D.isotropicVector η) b *
        D.normalCross a j η := by
    have hh := congrArg Matrix.transpose hfirst
    rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,hsym,
      ← Matrix.mul_assoc] at hh
    exact hh.trans (by ext i j; exact mul_comm _ _)
  have hm := D.mixed_fullCross_mem_radicalGram_range SA hF Z hZ hirred hx hT hdim hmax
    a b (hker ha) hb
  rw [hfirst,hsecond] at hm
  exact hm

end CoisotropicBasis.Data
end HessianTheorem11
