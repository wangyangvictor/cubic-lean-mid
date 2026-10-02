import HessianTheorem11.ReducedDominantOpen
import HessianTheorem11.ReducedKernelTangent
import HessianTheorem11.ReducedGenericImageTangent

/-! The dominant fiber-product dimension inequality is derived from generic
smoothness and generic differential rank, with actual polynomial equations.
Both projections are restricted to the same generic base open before a smooth
point of the source is selected. The remaining bound is linear algebra. -/

noncomputable section
set_option maxHeartbeats 2000000
namespace HessianTheorem11.ReducedDominantFiberProduct
open MvPolynomial Module ReducedKernelTangent ReducedGenericImageTangent

/-- An injective family of pairs satisfying A(v)=B(w) has the expected
upper dimension bound. No surjectivity of either map is assumed. -/
theorem linear_fiber_product_dimension_bound
    {K V E W T : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup W] [Module K W]
    [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    (A : V →ₗ[K] W) (B : E →ₗ[K] W) (J : T →ₗ[K] V × E)
    (hJ : Function.Injective J) (hrel : ∀ z, A (J z).1 = B (J z).2) :
    finrank K T + finrank K (LinearMap.range A) ≤ finrank K V + finrank K E := by
  let H : V × E →ₗ[K] W :=
    A.comp (LinearMap.fst K V E) - B.comp (LinearMap.snd K V E)
  have hker : LinearMap.range J ≤ LinearMap.ker H := by
    rintro _ ⟨z,rfl⟩
    exact sub_eq_zero.mpr (hrel z)
  have hrange : LinearMap.range A ≤ LinearMap.range H := by
    rintro _ ⟨v,rfl⟩
    refine ⟨(v,0),?_⟩
    simp [H]
  have hk := Submodule.finrank_mono hker
  have hr := Submodule.finrank_mono hrange
  rw [LinearMap.finrank_range_of_inj hJ] at hk
  have hd := H.finrank_range_add_finrank_ker
  rw [Module.finrank_prod] at hd
  omega

private theorem differential_sub {n : ℕ} (f g : GeometricPolynomial n)
    (x v : GeometricPoint n) :
    polynomialDifferential (f-g) x v =
      polynomialDifferential f x v - polynomialDifferential g x v := by
  simp only [polynomialDifferential_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

/-- Differentiating the actual equations P(Lx)=P(Rx), on the full embedded
tangent space of their solution set. -/
theorem differential_compatibility {n m q : ℕ}
    (P : Fin m → GeometricPolynomial n)
    (L R : GeometricPoint q →ₗ[GeometricField] GeometricPoint n)
    (Y : Set (GeometricPoint q))
    (hrel : ∀ y ∈ Y, polynomialMap P (L y) = polynomialMap P (R y))
    (x v : GeometricPoint q) (hv : v ∈ affineTangentSpace Y x) :
    polynomialMapDifferential P (L x) (L v) =
      polynomialMapDifferential P (R x) (R v) := by
  funext i
  have he : pullback L (P i) - pullback R (P i) ∈ vanishingIdeal GeometricField Y := by
    intro y hy
    change eval y (pullback L (P i) - pullback R (P i)) = 0
    rw [map_sub, eval_pullback, eval_pullback]
    exact sub_eq_zero.mpr (congrFun (hrel y hy) i)
  have hh := mem_affineTangentSpace.mp hv _ he
  rw [differential_sub, differential_pullback, differential_pullback] at hh
  exact sub_eq_zero.mp hh

/-- The full former dominant fiber-product interface, now from GR alone.
No dimension-of-fibers or additional geometry input is retained. -/
def dominantFiberProductInput (GR : GenericRankOpenInput) : DominantFiberProductInput where
  dimension_bound := by
    intro n m P U Y hU hiU hY hiY hleft hright hrel t s d ht hs hd
    let E := pairCoordinateEquiv n n
    let PE := PolynomialCoordinateEquiv.ofLinearEquiv E
    let Yc := E '' Y
    have hYc : AlgebraicallyClosedSet Yc := by
      simpa only [PE, PolynomialCoordinateEquiv.ofLinearEquiv_forwardMap] using
        (PE.algebraicallyClosedSet_image_iff Y).mpr hY
    have hiYc : GeometricallyIrreducible Yc := by
      simpa only [PE, PolynomialCoordinateEquiv.ofLinearEquiv_forwardMap] using
        (PE.geometricallyIrreducible_image_iff Y).mpr hiY
    have hdimYc : affineDimension Yc = (d : Dimension) := by
      have hh := PE.affineDimension_image Y
      simpa only [PE, PolynomialCoordinateEquiv.ofLinearEquiv_forwardMap, hd] using hh
    let L := baseProjection n n
    let R := fiberProjection n n
    let LP := linearCoordinatePolynomials L
    let RP := linearCoordinatePolynomials R
    have hLI : polynomialMap LP '' Yc = pairLeft '' Y := by
      ext x
      constructor
      · rintro ⟨z,⟨y,hy,rfl⟩,rfl⟩
        exact ⟨y,hy,by simp [LP,L,E]⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨E y,⟨y,hy,rfl⟩,by simp [LP,L,E]⟩
    have hRI : polynomialMap RP '' Yc = pairRight '' Y := by
      ext x
      constructor
      · rintro ⟨z,⟨y,hy,rfl⟩,rfl⟩
        exact ⟨y,hy,by simp [RP,R,E]⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨E y,⟨y,hy,rfl⟩,by simp [RP,R,E]⟩
    have hLD : geometricClosure (polynomialMap LP '' Yc) = U := hLI ▸ hleft
    have hRD : geometricClosure (polynomialMap RP '' Yc) = U := hRI ▸ hright
    have hLM : polynomialMap LP '' Yc ⊆ U := hLD ▸ subset_geometricClosure _
    have hRM : polynomialMap RP '' Yc ⊆ U := hRD ▸ subset_geometricClosure _
    have hrelc (z) (hz : z ∈ Yc) : polynomialMap P (L z) = polynomialMap P (R z) := by
      obtain ⟨y,hy,rfl⟩ := hz
      simpa [L,R,E] using hrel y hy
    obtain ⟨GU⟩ := GR.choose U hU hiU P
      (0 : GeometricPoint n →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
    obtain ⟨GY⟩ := GR.choose Yc hYc hiYc (fun _ : Fin 0 => 0)
      (0 : GeometricPoint (n+n) →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
    let OL := Yc ∩ polynomialMap LP ⁻¹' GU.openSet
    let OR := Yc ∩ polynomialMap RP ⁻¹' GU.openSet
    have hOL : RelativelyOpenSet Yc OL :=
      relativelyOpen_polynomial_preimage LP Yc GU.isOpen hLM
    have hOR : RelativelyOpenSet Yc OR :=
      relativelyOpen_polynomial_preimage RP Yc GU.isOpen hRM
    have hdOL : geometricClosure OL = Yc :=
      ReducedDominantOpen.dense_preimage LP Yc U GU.openSet hYc hiYc hLD GU.isOpen GU.dense
    have hdOR : geometricClosure OR = Yc :=
      ReducedDominantOpen.dense_preimage RP Yc U GU.openSet hYc hiYc hRD GU.isOpen GU.dense
    have hnLG : (OL ∩ GY.openSet).Nonempty :=
      dense_inter_open_nonempty hdOL GY.isOpen GY.nonempty
    obtain ⟨z,hzR,hzL,hzG⟩ :=
      dense_inter_open_nonempty hdOR (hOL.inter GY.isOpen) hnLG
    have hzLU : L z ∈ GU.openSet := by simpa [LP] using hzL.2
    have hzRU : R z ∈ GU.openSet := by simpa [RP] using hzR.2
    let TY := affineTangentSpace Yc z
    let TL := affineTangentSpace U (L z)
    let TR := affineTangentSpace U (R z)
    have hLT (v : TY) : L v ∈ TL := by
      have hh := differential_maps_tangent LP Yc U hLM z v v.property
      simpa only [LP, polynomialMap_linearCoordinatePolynomials,
        differential_linearCoordinates] using hh
    have hRT (v : TY) : R v ∈ TR := by
      have hh := differential_maps_tangent RP Yc U hRM z v v.property
      simpa only [RP, polynomialMap_linearCoordinatePolynomials,
        differential_linearCoordinates] using hh
    let J : TY →ₗ[GeometricField] TL × TR :=
      { toFun := fun v => (⟨L v,hLT v⟩,⟨R v,hRT v⟩)
        map_add' := by intro v w; apply Prod.ext <;> apply Subtype.ext <;> simp
        map_smul' := by intro c v; apply Prod.ext <;> apply Subtype.ext <;> simp }
    have hJ : Function.Injective J := by
      intro v w hh
      apply Subtype.ext
      apply (splitEquiv n n).injective
      exact Prod.ext (congrArg (fun p : TL × TR => p.1.val) hh)
        (congrArg (fun p : TL × TR => p.2.val) hh)
    let A := (polynomialMapDifferential P (L z)).domRestrict TL
    let B := (polynomialMapDifferential P (R z)).domRestrict TR
    have hAB (v : TY) : A (J v).1 = B (J v).2 :=
      differential_compatibility P L R Yc hrelc z v v.property
    have hbound := linear_fiber_product_dimension_bound A B J hJ hAB
    have hUt : GU.baseDimension = t := by exact_mod_cast GU.dimension_base.symm.trans ht
    have hUs : GU.imageDimension = s := by exact_mod_cast GU.dimension_image.symm.trans hs
    have hYd : GY.baseDimension = d := by exact_mod_cast GY.dimension_base.symm.trans hdimYc
    have hTY : finrank GeometricField TY = d := (GY.smooth z hzG).trans hYd
    have hTL : finrank GeometricField TL = t := (GU.smooth _ hzLU).trans hUt
    have hTR : finrank GeometricField TR = t := (GU.smooth _ hzRU).trans hUt
    have hA : finrank GeometricField (LinearMap.range A) = s :=
      (GU.differential_rank _ hzLU).trans hUs
    rw [hTY,hTL,hTR,hA] at hbound
    omega

end HessianTheorem11.ReducedDominantFiberProduct
