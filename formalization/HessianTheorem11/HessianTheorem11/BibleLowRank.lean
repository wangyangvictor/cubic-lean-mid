import HessianTheorem11.UnconditionalWeightDescent
import HessianTheorem11.ReducedClosedOrbitZero
import HessianTheorem11.BibleRankClosed
import HessianTheorem11.SmoothRadialDefect
import HessianTheorem11.SingularExceptionalComponent
import HessianTheorem11.RationalDescent

/-! The low-rank assertions of Bible Theorem I.1.1(i), proved for every
weight-semistable geometric cubic. All dimensions are affine dimensions of
the actual zero/rank loci. No new geometric input is introduced. -/
noncomputable section
namespace HessianTheorem11.BibleLowRank
open MvPolynomial Module Matrix

variable {n : ℕ}

theorem smooth_tangent_bound
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (x : GeometricPoint n)
    (T : Submodule GeometricField (GeometricPoint n)) (hxT : x ∈ T)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ T,
      ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin,
        polarization F t u v = 0)
    (hradial : ∀ t ∈ T, polarization F x x t = 0) :
    finrank GeometricField T + 2 ≤ 2 * (hessian F x).rank := by
  classical
  obtain ⟨E⟩ := smooth_radial_support_data F hF hsemi x T hxT hxL htensor hradial
  have hs := E.total_weight_nonnegative
  rw [sum_smoothRadialWeight] at hs
  have hi : E.adapted.tangentIndices ∩ E.adapted.kernelIndices ⊂
      E.adapted.tangentIndices := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro he
    have hm : E.adapted.radial ∈ E.adapted.tangentIndices ∩ E.adapted.kernelIndices := by
      rw [he]
      exact E.adapted.radial_mem_tangent
    exact E.adapted.radial_notMem_kernel (Finset.mem_inter.mp hm).2
  have hc := Finset.card_lt_card hi
  rw [E.adapted.tangent_card] at hc hs
  rw [E.adapted.kernel_card] at hs
  have hr := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  change (hessian F x).rank + _ = finrank GeometricField (GeometricPoint n) at hr
  rw [show finrank GeometricField (GeometricPoint n) = n by simp] at hr
  have hci : ((E.adapted.tangentIndices ∩ E.adapted.kernelIndices).card : ℤ) + 1 ≤
      (finrank GeometricField T : ℤ) := by exact_mod_cast hc
  have hri : ((hessian F x).rank : ℤ) +
      (finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) : ℤ) = (n : ℤ) := by
    exact_mod_cast hr
  have hb : (finrank GeometricField T : ℤ) + 2 ≤ 2 * ((hessian F x).rank : ℤ) := by
    linarith
  exact_mod_cast hb

/-- At a generic radial point, either branch gives t ≤ 2r−2. The singular
branch actually saves one more dimension. -/
theorem point_tangent_bound
    (DT : SymmetricDeterminantalTangentInput)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F)
    (Z : Set (GeometricPoint n)) (x : GeometricPoint n)
    (hxZ : x ∈ Z) (hx0 : x ≠ 0) (hxT : x ∈ affineTangentSpace Z x)
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (hcontained : ∀ y ∈ Z, eval y F = 0)
    (hgenericSing : gradient F x = 0 → ∀ y ∈ Z, gradient F y = 0) :
    finrank GeometricField (affineTangentSpace Z x) + 2 ≤ 2 * (hessian F x).rank := by
  have htensor := hessian_tangent_polarization_zero DT F hF Z x hxZ hmax
  by_cases hsing : gradient F x = 0
  · have hr := singular_radial_of_tensor_vanishing F hF hsemi x hx0
      (affineTangentSpace Z x) hxT
      (affineTangentSpace_le_hessian_ker F Z (hgenericSing hsing) x) htensor
    omega
  · exact smooth_tangent_bound F hF hsemi x (affineTangentSpace Z x) hxT
      (self_notMem_hessian_ker_of_gradient_ne_zero hF x hsing) htensor
      (fun t ht => polarization_self_self_tangent_zero hF Z hcontained x t ht)

theorem eval_cubic_smul (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (a : GeometricField) (x : GeometricPoint n) :
    eval (a • x) F = a ^ 3 * eval x F := by
  simp only [eval_cubic_eq_polarization hF, polarization_smul_first,
    polarization_smul_second, polarization_smul_third hF]
  ring

theorem hessian_rank_smul_le (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (a : GeometricField) (x : GeometricPoint n) :
    (hessian F (a • x)).rank ≤ (hessian F x).rank := by
  rw [hessian_smul hF, smul_eq_diagonal_mul]
  exact rank_mul_le_right _ _

def onCubicRankLocus (F : GeometricPolynomial n) (r : ℕ) : Set (GeometricPoint n) :=
  {x | eval x F = 0 ∧ (hessian F x).rank ≤ r}

theorem onCubicRankLocus_closed (F : GeometricPolynomial n) (r : ℕ) :
    AlgebraicallyClosedSet (onCubicRankLocus F r) := by
  apply Set.Subset.antisymm ?_ (subset_geometricClosure _)
  intro x hx
  refine ⟨hx F (fun _ hy => hy.1), ?_⟩
  have hc := polynomialMatrix_rank_locus_closed (hessianPolynomial F) r
  exact geometricClosure_subset_closed (fun _ hy => hy.2) hc hx

theorem onCubicRankLocus_cone (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (r : ℕ) : IsAffineCone (onCubicRankLocus F r) := by
  intro a x hx
  exact ⟨by rw [eval_cubic_smul F hF, hx.1, mul_zero],
    (hessian_rank_smul_le F hF a x).trans hx.2⟩

/-- There is no nonzero point on a weight-semistable cubic with Hessian
rank at most one. This uses the actual radial line through that point. -/
theorem on_cubic_rank_one_eq_origin
    (DT : SymmetricDeterminantalTangentInput)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) : onCubicRankLocus F 1 = {0} := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hx0
    have hxn : x ≠ 0 := hx0
    let S : Submodule GeometricField (GeometricPoint n) := Submodule.span GeometricField {x}
    have hxS : x ∈ S := Submodule.subset_span (Set.mem_singleton x)
    have hxT : x ∈ affineTangentSpace (S : Set (GeometricPoint n)) x :=
      submodule_le_affineTangentSpace_of_subset S S (fun _ h => h) x hxS hxS
    have hmax : ∀ y ∈ (S : Set (GeometricPoint n)),
        (hessian F y).rank ≤ (hessian F x).rank := by
      intro y hy
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
      exact hessian_rank_smul_le F hF a x
    have hcontained : ∀ y ∈ (S : Set (GeometricPoint n)), eval y F = 0 := by
      intro y hy
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [eval_cubic_smul F hF, hx.1, mul_zero]
    have hgeneric : gradient F x = 0 → ∀ y ∈ (S : Set (GeometricPoint n)),
        gradient F y = 0 := by
      intro h y hy
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
      ext i
      change eval (a • x) (pderiv i F) = 0
      rw [SingularNormalEquations.eval_quadratic_smul _ hF.pderiv]
      have hi := congrFun h i
      change eval x (pderiv i F) = 0 at hi
      rw [hi, mul_zero]
    have ht := point_tangent_bound DT F hF hsemi S x hxS hxn hxT hmax hcontained hgeneric
    have hr := hx.2
    have hz : affineTangentSpace (S : Set (GeometricPoint n)) x = ⊥ :=
      Submodule.finrank_eq_zero.mp (by omega)
    exact hxn (by simpa [hz] using hxT)
  · intro hx
    have hx' : x = 0 := hx
    subst x
    exact ⟨eval_origin_of_positive_homogeneous hF (by norm_num),
      by rw [hessian_zero hF, rank_zero]; omega⟩

/-- General affine rank-locus bound on a semistable cubic, obtained by
selecting a component of largest dimension and applying the radial weights. -/
theorem on_cubic_rank_dimension_le
    (AC : AffineComponentsInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (r : ℕ) (hr : 1 ≤ r) :
    affineDimension (onCubicRankLocus F r) ≤ ((2 * r - 2 : ℕ) : Dimension) := by
  have hclosed := onCubicRankLocus_closed F r
  have hcone := onCubicRankLocus_cone F hF r
  have hzero : (0 : GeometricPoint n) ∈ onCubicRankLocus F r := by
    exact ⟨eval_origin_of_positive_homogeneous hF (by norm_num),
      by rw [hessian_zero hF, rank_zero]; omega⟩
  obtain ⟨Z,hZ,hdim⟩ := AC.maximal_dimension_component _ hclosed ⟨0,hzero⟩
  rw [← hdim]
  by_cases hZ0 : Z ⊆ {0}
  · exact (affineDimension_mono hZ0).trans (by rw [affineDimension_singleton]; simp)
  · let P := GP.choose Z hZ.closed hZ.irreducible (hZ.isAffineCone AC hclosed hcone) hZ0
      (hessianLinearMap F hF) (fun i => pderiv i F)
    have hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F P.point).rank := P.rank_maximal
    have hgeneric : gradient F P.point = 0 → ∀ y ∈ Z, gradient F y = 0 := by
      intro h y hy
      have hp : P.point ∈ finiteEquationZeroSet (fun i => pderiv i F) := fun i => congrFun h i
      exact funext (P.detects_equations hp hy)
    have ht := point_tangent_bound DT F hF hsemi Z P.point P.member P.nonzero P.radial
      hmax (fun y hy => (hZ.subset hy).1) hgeneric
    have hrank : (hessian F P.point).rank ≤ r := (hZ.subset P.member).2
    rw [P.dimension]
    have hd : finrank GeometricField (affineTangentSpace Z P.point) ≤ 2 * r - 2 := by omega
    exact_mod_cast hd

theorem on_cubic_rank_two_dimension_le
    (AC : AffineComponentsInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) :
    affineDimension {x : GeometricPoint n | eval x F = 0 ∧ (hessian F x).rank ≤ 2} ≤ 2 := by
  simpa [onCubicRankLocus] using on_cubic_rank_dimension_le AC GP DT F hF hsemi 2 (by omega)

theorem anisotropic_on_cubic_rank_one_eq_origin
    (DT : SymmetricDeterminantalTangentInput)
    (F : AnisotropicCubic n) (hn : 0 < n) :
    {x ∈ cubicLocus F.polynomial | (hessian (geometricPolynomial F.polynomial) x).rank ≤ 1} = {0} :=
  on_cubic_rank_one_eq_origin DT _ (geometric_homogeneous F.homogeneous)
    (UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F hn)

theorem anisotropic_on_cubic_rank_two_dimension_le
    (AC : AffineComponentsInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput)
    (F : AnisotropicCubic n) (hn : 0 < n) :
    affineDimension {x ∈ cubicLocus F.polynomial |
      (hessian (geometricPolynomial F.polynomial) x).rank ≤ 2} ≤ 2 :=
  on_cubic_rank_two_dimension_le AC GP DT _ (geometric_homogeneous F.homogeneous)
    (UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F hn)

end HessianTheorem11.BibleLowRank
