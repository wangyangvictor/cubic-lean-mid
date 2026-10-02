import HessianTheorem11.Concentration
import HessianTheorem11.AffineHypersurfaceDimension
import HessianTheorem11.PolarizationExpansion

/-! Kernel saturation is derived from maximality of an actual concentration
base and the proved gradient fiber-product dimension squeeze. No statement
about linearity of exceptional Gauss fibers is used. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

theorem IsAffineCone.closure {σ : Type*} [Fintype σ]
    {Z : Set (σ → GeometricField)} (hZ : IsAffineCone Z) :
    IsAffineCone (geometricClosure Z) := by
  intro a x hx
  let P : σ → MvPolynomial σ GeometricField := fun i => C a * X i
  have hp : polynomialMap P = fun x : σ → GeometricField => a • x := by
    funext x i
    simp [P, polynomialMap]
  have hi : polynomialMap P '' Z ⊆ Z := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hp]
    exact hZ a y hy
  exact geometricClosure_mono hi
    (polynomialMap_image_closure_subset P Z ⟨x, hx, congrFun hp x⟩)

theorem IsAffineCone.linear_image {σ τ : Type*}
    {Z : Set (σ → GeometricField)} (hZ : IsAffineCone Z)
    (L : (σ → GeometricField) →ₗ[GeometricField] (τ → GeometricField)) :
    IsAffineCone (L '' Z) := by
  intro a y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨a • x, hZ a x hx, L.map_smul a x⟩

def pairLeftLinear (n m : ℕ) : PairPoint n m →ₗ[GeometricField] GeometricPoint n where
  toFun := pairLeft
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem IsBicone.isAffineCone {n m : ℕ} {Z : Set (PairPoint n m)}
    (hZ : IsBicone Z) : IsAffineCone Z := by
  intro a p hp
  have h := hZ p hp a a
  convert h using 1
  ext (i | i) <;> rfl

/-- The mixed terms vanish for an actual Hessian-incidence pair. -/
theorem cubic_add_of_incidence {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (x y : GeometricPoint n)
    (hxy : (hessian F x).mulVec y = 0) :
    eval (x + y) F = eval x F + eval y F := by
  rw [eval_cubic_add hF]
  have h1 : polarization F x x y = 0 := by
    rw [polarization_swap_last hF]
    simp [polarization, hxy]
  have h2 : polarization F x y y = 0 := by
    rw [polarization_rotate hF, polarization_swap_last hF]
    simp [polarization, hxy]
  simp [h1, h2]

/-- A maximal-dimensional concentration base exists by ordinary bounded
maximization of natural numbers; no special geometric maximality is input. -/
theorem exists_maximal_concentration_base
    (AG : ConcentrationGeometryInput) (DT : SymmetricDeterminantalTangentInput)
    (AD : AffineHypersurfaceDimensionInput) {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (hirred : Irreducible F) :
    ∃ C : IncidenceConcentration F, ∀ C' : IncidenceConcentration F,
      C'.baseDimension ≤ C.baseDimension := by
  let S : Set ℕ := {d | ∃ C : IncidenceConcentration F, C.baseDimension = d}
  have hs : S.Nonempty := by
    obtain ⟨C⟩ := incidence_concentration AG DT F hF
    exact ⟨C.baseDimension, C, rfl⟩
  have hb : BddAbove S := by
    refine ⟨n - 1, ?_⟩
    rintro d ⟨C, rfl⟩
    have hd := affineDimension_mono (show C.base ⊆ polynomialHypersurface F from C.contained)
    rw [C.dimension_base, AD.hypersurface F hirred] at hd
    exact_mod_cast hd
  obtain ⟨C, hC⟩ := Nat.sSup_mem hs hb
  refine ⟨C, ?_⟩
  intro C'
  rw [hC]
  exact le_csSup hb (show C'.baseDimension ∈ S from ⟨C', rfl⟩)

/-- The generic matrix data of a concentrated base retain exactly the
incidence dimension; no choice of the dense open changes the generic rank. -/
theorem IncidenceConcentration.generic_bundle_dimension {n : ℕ}
    (AG : ConcentrationGeometryInput) (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (C : IncidenceConcentration F)
    (G : GenericRankOpen C.base (fun i => pderiv i F) (hessianLinearMap F hF)) :
    affineDimension (kernelBundle (hessianLinearMap F hF) G.openSet) =
      affineDimension (cubicIncidence F) := by
  have ht : G.baseDimension = C.baseDimension := by
    have hd := G.dimension_base.symm.trans C.dimension_base
    exact_mod_cast hd
  obtain ⟨x, hx⟩ := G.nonempty
  have hr : (hessian F x).rank = C.rank := by
    apply le_antisymm (C.maximal_rank x (G.subset hx))
    obtain ⟨y, hy, hyr⟩ := C.rank_attained
    have h := G.maximal_rank x hx y hy
    change (hessian F y).rank ≤ _ at h
    rwa [hyr] at h
  have hn := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  have hk : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = G.nullity :=
    G.kernel_dimension x hx
  change (hessian F x).rank + _ = _ at hn
  have hn' : C.rank + G.nullity = n := by simpa [hr, hk] using hn
  have hl : G.nullity = C.nullity := by have h := C.rank_nullity; omega
  rw [AG.dimension (hessianLinearMap F hF) C.base G.openSet C.closed C.irreducible
    G.isOpen G.dense G.baseDimension G.nullity G.dimension_base G.kernel_dimension]
  rw [ht, hl, C.dimension_incidence]

def pairSumPolynomials (n : ℕ) : Fin n → MvPolynomial (Fin n ⊕ Fin n) GeometricField :=
  fun i => X (Sum.inl i) + X (Sum.inr i)

@[simp] theorem polynomialMap_pairSumPolynomials {n : ℕ} (p : PairPoint n n) :
    polynomialMap (pairSumPolynomials n) p = pairLeft p + pairRight p := by
  ext i
  simp [polynomialMap, pairSumPolynomials, pairLeft, pairRight]

/-- Repackage actual full-kernel-bundle data as a concentration base. -/
def concentrationOfGenericBundle {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (U : Set (GeometricPoint n)) (hUc : AlgebraicallyClosedSet U)
    (hUi : GeometricallyIrreducible U) (hUcone : IsAffineCone U)
    (hUF : ∀ x ∈ U, eval x F = 0)
    (G : GenericRankOpen U (fun i => pderiv i F) (hessianLinearMap F hF))
    (hDim : affineDimension (cubicIncidence F) =
      ((G.baseDimension + G.nullity : ℕ) : Dimension)) : IncidenceConcentration F := by
  let x := Classical.choose G.nonempty
  have hx := Classical.choose_spec G.nonempty
  refine {
    base := U
    closed := hUc
    irreducible := hUi
    cone := hUcone
    contained := hUF
    baseDimension := G.baseDimension
    rank := (hessian F x).rank
    nullity := G.nullity
    dimension_base := G.dimension_base
    dimension_incidence := hDim
    rank_nullity := ?_
    rank_attained := ⟨x, G.subset hx, rfl⟩
    maximal_rank := G.maximal_rank x hx
  }
  have hr := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  have hk : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = G.nullity :=
    G.kernel_dimension x hx
  change (hessian F x).rank + _ = _ at hr
  simpa [hk] using hr

/-- Shearing the full kernel bundle creates a concentration base containing
the old base and every generic translate by its actual Hessian kernel. -/
theorem exists_concentration_containing_kernel_translates
    (AG : ConcentrationGeometryInput) (DT : SymmetricDeterminantalTangentInput)
    {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (C : IncidenceConcentration F)
    (G : GenericRankOpen C.base (fun i => pderiv i F) (hessianLinearMap F hF))
    (hKT : ∀ x ∈ G.openSet,
      LinearMap.ker (hessian F x).mulVecLin ≤ affineTangentSpace C.base x) :
    ∃ C' : IncidenceConcentration F, C.base ⊆ C'.base ∧
      ∀ x ∈ G.openSet, ∀ y ∈ LinearMap.ker (hessian F x).mulVecLin, x + y ∈ C'.base := by
  let M := hessianLinearMap F hF
  let B := kernelBundle M G.openSet
  let W := geometricClosure B
  have hWc : AlgebraicallyClosedSet W := algebraicallyClosedSet_geometricClosure _
  have hWi : GeometricallyIrreducible W := AG.closure_irreducible M C.base G.openSet
    C.closed C.irreducible G.isOpen G.dense G.nullity G.kernel_dimension
  have hWI : W ⊆ cubicIncidence F := geometricClosure_subset_closed
    (kernelBundle_subset_cubicIncidence F hF G.openSet) (cubicIncidence_closed F)
  have hWdim : affineDimension W = affineDimension (cubicIncidence F) := by
    rw [affineDimension_closure]
    exact C.generic_bundle_dimension AG F hF G
  have hWcomp := AG.dimension_maximal (cubicIncidence F) W (cubicIncidence_closed F)
    hWc hWi hWI hWdim
  have hWbi := AG.bicone_component (cubicIncidence F) W (cubicIncidence_closed F)
    (cubicIncidence_bicone F hF) hWcomp
  have hkernelzero : ∀ x ∈ G.openSet, ∀ y ∈ LinearMap.ker (hessian F x).mulVecLin,
      eval y F = 0 := by
    intro x hx
    apply cubic_vanishes_on_kernel_of_tangent_containment F hF x
      (affineTangentSpace C.base x) (hKT x hx)
    intro t ht u hu v hv
    have hp := DT.tangent_kernel_pairing M (hessian_symmetric F) C.base x
      (G.subset hx) (G.maximal_rank x hx) t ht u hu v hv
    rw [polarization_swap_first, polarization_swap_last hF]
    exact hp
  have hsumzero : ∀ p ∈ W, eval (pairLeft p + pairRight p) F = 0 := by
    have hb : ∀ p ∈ B, eval p (aeval (pairSumPolynomials n) F) = 0 := by
      intro p hp
      rw [← eval_polynomialMap, polynomialMap_pairSumPolynomials]
      rw [cubic_add_of_incidence F hF _ _ hp.2,
        C.contained _ (G.subset hp.1), hkernelzero _ hp.1 _ hp.2, add_zero]
    have hc := geometricClosure_subset_of_polynomial_vanishes B
      (aeval (pairSumPolynomials n) F) hb
    intro p hp
    have h := hc p hp
    rwa [← eval_polynomialMap, polynomialMap_pairSumPolynomials] at h
  let E := PolynomialCoordinateEquiv.ofLinearEquiv (incidenceSumCoordinateChange n)
  let Y := incidenceSumCoordinateChange n '' W
  have hYc : AlgebraicallyClosedSet Y := by
    simpa [E, Y] using (E.algebraicallyClosedSet_image_iff W).mpr hWc
  have hYi : GeometricallyIrreducible Y := by
    simpa [E, Y] using (E.geometricallyIrreducible_image_iff W).mpr hWi
  have hYdim : affineDimension Y = affineDimension (cubicIncidence F) := by
    calc
      affineDimension Y = affineDimension W := by simpa [E, Y] using E.affineDimension_image W
      _ = affineDimension (cubicIncidence F) := hWdim
  let U := geometricClosure (pairLeft '' Y)
  have hUc : AlgebraicallyClosedSet U := algebraicallyClosedSet_geometricClosure _
  have hUi : GeometricallyIrreducible U := by
    apply (geometricallyIrreducible_closure_iff _).mpr
    simpa using hYi.polynomialMap_image (pairLeftPolynomials n n)
  have hUcone : IsAffineCone U := by
    apply IsAffineCone.closure
    exact (hWbi.isAffineCone.linear_image (incidenceSumCoordinateChange n).toLinearMap).linear_image
      (pairLeftLinear n n)
  have hUF : ∀ x ∈ U, eval x F = 0 := by
    apply geometricClosure_subset_of_polynomial_vanishes (pairLeft '' Y) F
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact hsumzero p hp
  let Gu := Classical.choice (AG.choose U hUc hUi (fun i => pderiv i F) M)
  have hequal : geometricClosure (pairRight '' Y) = U := by
    unfold U Y
    rw [incidenceSumCoordinateChange_equal_projections W hWbi]
  have hrelation : ∀ p ∈ Y, gradient F (pairLeft p) = gradient F (pairRight p) :=
    incidenceSumCoordinateChange_equal_gradients F hF W hWI
  obtain ⟨hBdim, _⟩ := gradient_fiber_product_kernel_vanishing AG DT F hF Y
    hYc hYi hYdim hequal hrelation Gu
  have hDim : affineDimension (cubicIncidence F) =
      ((Gu.baseDimension + Gu.nullity : ℕ) : Dimension) := by
    rw [← hBdim]
    exact AG.dimension M U Gu.openSet hUc hUi Gu.isOpen Gu.dense
      Gu.baseDimension Gu.nullity Gu.dimension_base Gu.kernel_dimension
  let C' := concentrationOfGenericBundle F hF U hUc hUi hUcone hUF Gu hDim
  have hC' : C'.base = U := rfl
  have htranslate : ∀ x ∈ G.openSet, ∀ y ∈ LinearMap.ker (hessian F x).mulVecLin,
      x + y ∈ U := by
    intro x hx y hy
    apply subset_geometricClosure _
    refine ⟨incidenceSumCoordinateChange n (pairPoint x y), ?_, rfl⟩
    exact ⟨pairPoint x y, subset_geometricClosure B ⟨hx, hy⟩, rfl⟩
  refine ⟨C', ?_, ?_⟩
  · rw [hC']
    have hopen : G.openSet ⊆ U := by
      intro x hx
      simpa using htranslate x hx 0 (Submodule.zero_mem _)
    rw [← G.dense]
    exact geometricClosure_subset_closed hopen hUc
  · rw [hC']
    exact htranslate

/-- Polynomial closedness fills the missing parameter of an affine line.
The proof is polynomial identity on the infinite set of nonzero scalars. -/
theorem closed_contains_missing_line_point {n : ℕ} (Z : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) (x y : GeometricPoint n)
    (hline : ∀ a : GeometricField, a ≠ 0 → a • x + y ∈ Z) : y ∈ Z := by
  rw [← hZ]
  intro P hP
  let L : Fin n → MvPolynomial (Fin 1) GeometricField :=
    fun i => C (x i) * X 0 + C (y i)
  let Q : MvPolynomial (Fin 1) GeometricField := aeval L P
  have heval (v : Fin 1 → GeometricField) : eval v Q = eval (v 0 • x + y) P := by
    change eval v (aeval L P) = eval (v 0 • x + y) P
    rw [← eval_polynomialMap]
    have hp : polynomialMap L v = v 0 • x + y := by
      funext i
      simp [polynomialMap, L, mul_comm]
    rw [hp]
  have hQ : Q = 0 := by
    apply MvPolynomial.funext_set (fun _ : Fin 1 => ({0} : Set GeometricField)ᶜ)
      (fun _ => (Set.finite_singleton 0).infinite_compl)
    intro v hv
    rw [heval, map_zero]
    exact hP _ (hline (v 0) (by simpa using hv 0 (Set.mem_univ 0)))
  have hz := congrArg (eval (0 : Fin 1 → GeometricField)) hQ
  rw [heval] at hz
  simpa using hz

/-- Maximality of the projection dimension forces every generic kernel
translate to remain in the original base. -/
theorem maximal_concentration_contains_kernel_translates
    (AG : ConcentrationGeometryInput) (DT : SymmetricDeterminantalTangentInput)
    (AD : AffineHypersurfaceDimensionInput)
    {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (C : IncidenceConcentration F)
    (hmax : ∀ C' : IncidenceConcentration F, C'.baseDimension ≤ C.baseDimension)
    (G : GenericRankOpen C.base (fun i => pderiv i F) (hessianLinearMap F hF))
    (hKT : ∀ x ∈ G.openSet,
      LinearMap.ker (hessian F x).mulVecLin ≤ affineTangentSpace C.base x) :
    ∀ x ∈ G.openSet, ∀ y ∈ LinearMap.ker (hessian F x).mulVecLin, x + y ∈ C.base := by
  obtain ⟨C', hsub, htrans⟩ := exists_concentration_containing_kernel_translates AG DT F hF C G hKT
  have heq : C.base = C'.base := by
    by_contra hne
    have hlt := AD.proper_closed C.base C'.base C.closed C'.closed C'.irreducible
      (Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    rw [C.dimension_base, C'.dimension_base] at hlt
    have hdim : C.baseDimension < C'.baseDimension := by exact_mod_cast hlt
    exact (not_lt_of_ge (hmax C')) hdim
  intro x hx y hy
  simpa only [← heq] using htrans x hx y hy

/-- Source kernel saturation: the actual linear space `kx + ker(Hx)` lies
in a maximal concentration base at every point of the specified generic
open where the kernel lies in the tangent space. -/
theorem maximal_concentration_kernel_saturation
    (AG : ConcentrationGeometryInput) (DT : SymmetricDeterminantalTangentInput)
    (AD : AffineHypersurfaceDimensionInput)
    {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (C : IncidenceConcentration F)
    (hmax : ∀ C' : IncidenceConcentration F, C'.baseDimension ≤ C.baseDimension)
    (G : GenericRankOpen C.base (fun i => pderiv i F) (hessianLinearMap F hF))
    (hKT : ∀ x ∈ G.openSet,
      LinearMap.ker (hessian F x).mulVecLin ≤ affineTangentSpace C.base x) :
    ∀ x ∈ G.openSet, ∀ a : GeometricField,
      ∀ y ∈ LinearMap.ker (hessian F x).mulVecLin, a • x + y ∈ C.base := by
  have htrans := maximal_concentration_contains_kernel_translates AG DT AD F hF C hmax G hKT
  intro x hx a y hy
  have hnonzero : ∀ b : GeometricField, b ≠ 0 → b • x + y ∈ C.base := by
    intro b hb
    have hy' : b⁻¹ • y ∈ LinearMap.ker (hessian F x).mulVecLin :=
      Submodule.smul_mem _ _ hy
    have h := C.cone b _ (htrans x hx _ hy')
    simpa only [smul_add, smul_smul, mul_inv_cancel₀ hb, one_smul] using h
  by_cases ha : a = 0
  · subst a
    simpa using closed_contains_missing_line_point C.base C.closed x y hnonzero
  · exact hnonzero a ha

end HessianTheorem11
