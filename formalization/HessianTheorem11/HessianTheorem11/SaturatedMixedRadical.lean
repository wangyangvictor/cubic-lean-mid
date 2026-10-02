import HessianTheorem11.SaturatedMixedSchur
import HessianTheorem11.TwoDimensionalSymmetricProducts
import HessianTheorem11.CoisotropicMiddleBasis

/-! The actual normal pencil has the kernel of the mixed pairing in its
common radical. This joins source Lemmas 34.4 and 34.5. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

namespace CoisotropicBasis.Data
variable {n m q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m 2 q)

def radicalFormLinear (hF : F.IsHomogeneous 3) :
    GeometricPoint n →ₗ[GeometricField]
      LinearMap.BilinForm GeometricField (GeometricPoint m) :=
  Matrix.toBilin'.toLinearMap.comp
    (polarizationBlockLinear F hF D.radicalVector D.radicalVector)

theorem radicalFormLinear_apply (hF : F.IsHomogeneous 3)
    (y : GeometricPoint n) (a b : GeometricPoint m) :
    D.radicalFormLinear hF y a b =
      polarization F (D.radicalMatrix.mulVec a) (D.radicalMatrix.mulVec b) y := by
  have he (c : GeometricPoint m) : D.radicalMatrix.mulVec c = ∑ i, c i • D.radicalVector i := by
    ext j
    simp [radicalMatrix,Matrix.mulVec,dotProduct,mul_comm]
  rw [he a,he b]
  change Matrix.toBilin' (D.radicalGramAt y) a b = _
  simp only [Matrix.toBilin'_apply,polarization_sum_first,polarization_sum_second,
    polarization_smul_first,polarization_smul_second,radicalGramAt,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem radicalFormLinear_range_finrank_le (hF : F.IsHomogeneous 3)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0) :
    finrank GeometricField (LinearMap.range (D.radicalFormLinear hF)) ≤ 2 := by
  rw [radicalFormLinear,LinearMap.range_comp,LinearEquiv.finrank_map_eq]
  exact D.radicalGram_range_finrank_le hF hann

theorem normalCross_radical_form (hF : F.IsHomogeneous 3)
    (a : GeometricPoint m) (i : Fin m) (η : Fin 2) :
    D.normalCross (D.radicalMatrix.mulVec a) i η =
      D.radicalFormLinear hF (D.dualVector η) a (Pi.single i 1) := by
  rw [D.radicalFormLinear_apply hF,Matrix.mulVec_single_one]
  change polarization F (D.radicalVector i) (D.dualVector η) (D.radicalMatrix.mulVec a) =
    polarization F (D.radicalMatrix.mulVec a) (D.radicalVector i) (D.dualVector η)
  exact polarization_rotate hF _ _ _

theorem normal_form_ne_zero_of_full_cross (hF : F.IsHomogeneous 3)
    (a : GeometricPoint m) (hrank : (D.normalCross (D.radicalMatrix.mulVec a)).rank = 2)
    (η : Fin 2) : D.radicalFormLinear hF (D.dualVector η) ≠ 0 := by
  intro hz
  obtain ⟨L,hL⟩ := exists_left_inverse_of_full_column_rank _ hrank
  have he := congrFun (congrFun hL η) η
  have hc (i : Fin m) : D.normalCross (D.radicalMatrix.mulVec a) i η = 0 := by
    rw [D.normalCross_radical_form hF,hz]
    rfl
  simpa [Matrix.mul_apply,hc,Matrix.one_apply] using he

theorem middleMatrix_mem_tangent (b : GeometricPoint q) : D.middleMatrix.mulVec b ∈ T := by
  rw [D.middleMatrix_mulVec_sum]
  exact T.sum_mem fun i _ => T.smul_mem _ (D.tangent_middle i)

theorem toBilin_product_entries
    (u v : Module.Dual GeometricField (GeometricPoint m)) :
    Matrix.toBilin' (fun i j =>
      u (Pi.single i 1) * v (Pi.single j 1) + v (Pi.single i 1) * u (Pi.single j 1)) =
      TwoDimensionalSymmetricProducts.product u v := by
  apply LinearMap.BilinForm.toMatrix'.injective
  change LinearMap.BilinForm.toMatrix' (LinearMap.BilinForm.toMatrix'.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  ext i j
  rw [LinearMap.BilinForm.toMatrix'_apply,TwoDimensionalSymmetricProducts.product_apply]

/-- Any actual rank-two mixed pairing forces the two normal quadratic
forms to have the kernel of that pairing in their common radical. -/
theorem common_normal_radical_of_pairing_rank_two (SA : FormalSmoothArcInput)
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
    (a₀ : GeometricPoint m) (ha₀ : (D.normalCross (D.radicalMatrix.mulVec a₀)).rank = 2)
    (β : LinearMap.BilinForm GeometricField (GeometricPoint q))
    (hβs : β.IsSymm) (hβ : β.Nondegenerate)
    (e : GeometricPoint m →ₗ[GeometricField] GeometricPoint q)
    (he : finrank GeometricField (LinearMap.range e) = 2)
    (hpair : ∀ a b, β (e a) b = polarization F (D.radicalMatrix.mulVec a)
      (D.isotropicVector η) (D.middleMatrix.mulVec b)) :
    ∀ z ∈ LinearMap.ker e, ∀ a y,
      polarization F (D.radicalMatrix.mulVec z) (D.radicalMatrix.mulVec a) y = 0 := by
  classical
  let U := LinearMap.range e.dualMap
  let P := LinearMap.range (D.radicalFormLinear hF)
  let Q := D.radicalFormLinear hF (D.dualVector η)
  have hU : finrank GeometricField U = 2 := by
    rw [LinearMap.finrank_range_dualMap_eq_finrank_range]
    exact he
  have hP : finrank GeometricField P ≤ 2 := D.radicalFormLinear_range_finrank_le hF hann
  have hQ : Q ∈ P := ⟨D.dualVector η,rfl⟩
  have hQ0 : Q ≠ 0 := D.normal_form_ne_zero_of_full_cross hF a₀ ha₀ η
  have hmixed : ∀ u ∈ U, ∀ a, TwoDimensionalSymmetricProducts.product u (Q a) ∈ P := by
    intro u hu a
    obtain ⟨l,hl⟩ := hu
    obtain ⟨b,hb⟩ := (β.toDual hβ).surjective l
    have huval (v : GeometricPoint m) : u v =
        polarization F (D.radicalMatrix.mulVec v) (D.isotropicVector η) (D.middleMatrix.mulVec b) := by
      rw [← hl,← hb]
      change β b (e v) = _
      rw [hβs.eq,hpair]
    have hcol (i : Fin m) : u (Pi.single i 1) =
        polarization F (D.radicalVector i) (D.isotropicVector η) (D.middleMatrix.mulVec b) := by
      rw [huval,Matrix.mulVec_single_one]
      rfl
    have hm := D.two_normal_mixed_identity SA hF hann hker Z hZ hirred hx hT hdim hmax η hη
      (D.radicalMatrix.mulVec a) (D.middleMatrix.mulVec b)
      (D.radicalMatrix_mem_kernel a) (D.middleMatrix_mem_tangent b)
    obtain ⟨y,hy⟩ := hm
    refine ⟨y,?_⟩
    change Matrix.toBilin' _ = _
    rw [hy]
    rw [← toBilin_product_entries u (Q a)]
    apply congrArg Matrix.toBilin'
    ext i j
    have hnorm (i : Fin m) : Q a (Pi.single i 1) =
        D.normalCross (D.radicalMatrix.mulVec a) i η :=
      (D.normalCross_radical_form hF a i η).symm
    rw [hcol,hcol,hnorm,hnorm]
    ring
  have hc := TwoDimensionalSymmetricProducts.common_radical U hU P hP Q hQ hQ0 hmixed
  intro z hz a y
  have hzU : ∀ u ∈ U, u z = 0 := by
    rintro u ⟨l,rfl⟩
    change l (e z) = 0
    rw [show e z = 0 from hz,map_zero]
  have hh := congrArg (fun l : Module.Dual GeometricField (GeometricPoint m) => l a)
    (hc z hzU (D.radicalFormLinear hF y) ⟨y,rfl⟩)
  simpa only [D.radicalFormLinear_apply hF,LinearMap.zero_apply] using hh

end CoisotropicBasis.Data
end HessianTheorem11
