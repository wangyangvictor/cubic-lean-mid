import HessianTheorem11.CubicCoisotropicBasis
import HessianTheorem11.BasisHessianTransport

/-! The exact affine Hessian pencil on a saturated kernel line, in the
constructed coisotropic basis. Every complementary-block remainder is retained. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module
namespace CoisotropicBasis.Data
variable {K : Type*} [Field K] [CharZero K] {n m d q : ℕ}
  {F : MvPolynomial (Fin n) K} {x : Fin n → K} {T : Submodule K (Fin n → K)}
  (D : Data (hessianBilinear F x) T x m d q)

def radicalVector (i : Fin m) := D.basis (Sum.inl i)
def middleVector (i : Fin q) := D.basis (Sum.inr (Sum.inl i))
def isotropicVector (i : Fin d) := D.basis (Sum.inr (Sum.inr (Sum.inl i)))
def dualVector (i : Fin d) := D.basis (Sum.inr (Sum.inr (Sum.inr i)))
def complementVector (i : CoisotropicBasis.NondegenerateIndex d q) := D.basis (Sum.inr i)

def gramAt (y : Fin n → K) : Matrix (CoisotropicBasis.Index m d q)
    (CoisotropicBasis.Index m d q) K :=
  fun i j => polarization F (D.basis i) (D.basis j) y

def middleGram : Matrix (Fin q) (Fin q) K :=
  fun i j => polarization F (D.middleVector i) (D.middleVector j) x

def complementGramAt (y : Fin n → K) : Matrix (CoisotropicBasis.NondegenerateIndex d q)
    (CoisotropicBasis.NondegenerateIndex d q) K :=
  fun i j => polarization F (D.complementVector i) (D.complementVector j) y

def normalCross (a : Fin n → K) : Matrix (Fin m) (Fin d) K :=
  fun i j => polarization F (D.radicalVector i) (D.dualVector j) a

def crossAt (a : Fin n → K) : Matrix (Fin m) (CoisotropicBasis.NondegenerateIndex d q) K :=
  fun i => Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun j => D.normalCross a i j))

theorem middleGram_det_ne_zero : D.middleGram.det ≠ 0 := by
  have h := D.middle_nonsingular
  simpa only [middleGram, middleVector, hessianBilinear_apply] using h

theorem complementGramAt_base : D.complementGramAt x =
    fromBlocks D.middleGram 0 0 (fromBlocks (0 : Matrix (Fin d) (Fin d) K) 1 1 0) := by
  classical
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  · rfl
  · simpa only [hessianBilinear_apply] using D.middle_orthogonal_left i j
  · simpa only [hessianBilinear_apply] using D.middle_orthogonal_right i j
  · change polarization F (D.isotropicVector i) (D.middleVector j) x = 0
    rw [polarization_swap_first]
    simpa only [hessianBilinear_apply] using D.middle_orthogonal_left j i
  · simpa only [hessianBilinear_apply] using D.isotropic_left i j
  · simpa only [hessianBilinear_apply] using D.pairing i j
  · change polarization F (D.dualVector i) (D.middleVector j) x = 0
    rw [polarization_swap_first]
    simpa only [hessianBilinear_apply] using D.middle_orthogonal_right j i
  · change polarization F (D.dualVector i) (D.isotropicVector j) x = _
    rw [polarization_swap_first]
    simpa only [Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₁,
      Matrix.one_apply, eq_comm, hessianBilinear_apply] using D.pairing j i
  · simpa only [hessianBilinear_apply] using D.isotropic_right i j

theorem gramAt_base : D.gramAt x =
    fromBlocks (0 : Matrix (Fin m) (Fin m) K) 0 0 (D.complementGramAt x) := by
  ext i j
  cases i with
  | inl i =>
    have h := D.radical_vectors i
    have he := congrArg (fun f : (Fin n → K) →ₗ[K] K => f (D.basis j)) h
    change hessianBilinear F x (D.basis (Sum.inl i)) (D.basis j) = 0 at he
    rw [hessianBilinear_apply] at he
    cases j <;> exact he
  | inr i =>
    cases j with
    | inl j =>
      change polarization F _ _ x = 0
      rw [polarization_swap_first]
      have h := D.radical_vectors j
      have he := congrArg (fun f : (Fin n → K) →ₗ[K] K => f (D.basis (Sum.inr i))) h
      change hessianBilinear F x _ _ = 0 at he
      rwa [hessianBilinear_apply] at he
    | inr j => rfl

theorem cross_radical_tangent_zero (hF : F.IsHomogeneous 3)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (a : Fin n → K) (ha : a ∈ LinearMap.ker (hessian F x).mulVecLin)
    (i : Fin m) (v : Fin n → K) (hv : v ∈ T) :
    polarization F (D.radicalVector i) v a = 0 := by
  rw [polarization_swap_first]
  exact hann v hv _ (D.radical_hessian_kernel i) a ha

theorem gramAt_radical (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (a : Fin n → K) (ha : a ∈ LinearMap.ker (hessian F x).mulVecLin) :
    D.gramAt a = fromBlocks (0 : Matrix (Fin m) (Fin m) K)
      (D.crossAt a) (D.crossAt a).transpose (D.complementGramAt a) := by
  ext i j
  rcases i with i | (i | (i | i)) <;> rcases j with j | (j | (j | j))
  · exact D.cross_radical_tangent_zero hF hann a ha i _ (hker (D.radical_hessian_kernel j))
  · exact D.cross_radical_tangent_zero hF hann a ha i _ (D.tangent_middle j)
  · exact D.cross_radical_tangent_zero hF hann a ha i _ (D.tangent_isotropic j)
  · rfl
  · change polarization F _ _ a = 0
    rw [polarization_swap_first]
    exact D.cross_radical_tangent_zero hF hann a ha j _ (D.tangent_middle i)
  · rfl
  · rfl
  · rfl
  · change polarization F _ _ a = 0
    rw [polarization_swap_first]
    exact D.cross_radical_tangent_zero hF hann a ha j _ (D.tangent_isotropic i)
  · rfl
  · rfl
  · rfl
  · exact polarization_swap_first F _ _ a
  · rfl
  · rfl
  · rfl

theorem gramAt_line (hF : F.IsHomogeneous 3) (a : Fin n → K) (t : K) :
    D.gramAt (x+t • a) = D.gramAt x + t • D.gramAt a := by
  ext i j
  exact (polarization_add_third hF _ _ _ _).trans
    (congrArg (polarization F (D.basis i) (D.basis j) x + ·)
      (polarization_smul_third hF _ _ _ _))

theorem radial_row_complementGramAt_zero (hF : F.IsHomogeneous 3)
    (a : Fin n → K) (ha : a ∈ LinearMap.ker (hessian F x).mulVecLin)
    (j : CoisotropicBasis.NondegenerateIndex d q) :
    D.complementGramAt a (Sum.inr (Sum.inl D.radial)) j = 0 := by
  change polarization F (D.basis (Sum.inr (Sum.inr (Sum.inl D.radial))))
    (D.complementVector j) a = 0
  rw [D.radial_eq, polarization_swap_first, polarization_swap_last hF]
  change dotProduct (D.complementVector j) ((hessian F x).mulVec a) = 0
  rw [show (hessian F x).mulVec a = 0 from ha]
  simp

theorem exact_saturated_pencil (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (a : Fin n → K) (ha : a ∈ LinearMap.ker (hessian F x).mulVecLin) (t : K) :
    D.gramAt (x+t • a) = fromBlocks (0 : Matrix (Fin m) (Fin m) K)
      (t • D.crossAt a) (t • (D.crossAt a).transpose)
      (D.complementGramAt x + t • D.complementGramAt a) := by
  rw [D.gramAt_line hF, D.gramAt_base, D.gramAt_radical hF hker hann a ha]
  ext i j
  cases i <;> cases j <;> simp

end CoisotropicBasis.Data

namespace CoisotropicBasis.Data
variable {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d q)

theorem gramAt_eq_congruence (y : GeometricPoint n) :
    D.gramAt y = (BasisHessianTransport.basisMatrix D.basis).transpose *
      hessian F y * BasisHessianTransport.basisMatrix D.basis := by
  classical
  ext i j
  simp only [gramAt, polarization, dotProduct, Matrix.mulVec, Matrix.mul_apply,
    Matrix.transpose_apply, BasisHessianTransport.basisMatrix, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem gramAt_rank (y : GeometricPoint n) : (D.gramAt y).rank = (hessian F y).rank := by
  rw [D.gramAt_eq_congruence]
  exact BasisHessianTransport.rank_congruence_basis D.basis (hessian F y)

theorem exact_saturated_pencil_rank_le (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (Z : Set (GeometricPoint n))
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (hsat : ∀ t : GeometricField, ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin,
      x+t • a ∈ Z)
    (a : GeometricPoint n) (ha : a ∈ LinearMap.ker (hessian F x).mulVecLin) (t : GeometricField) :
    (fromBlocks (0 : Matrix (Fin m) (Fin m) GeometricField)
      (t • D.crossAt a) (t • (D.crossAt a).transpose)
      (D.complementGramAt x + t • D.complementGramAt a)).rank ≤ q+2*d := by
  rw [← D.exact_saturated_pencil hF hker hann a ha t, D.gramAt_rank]
  have hh := hmax (x+t • a) (hsat t a ha)
  have hd := D.hessian_dimensions.2
  omega

end CoisotropicBasis.Data
end HessianTheorem11
