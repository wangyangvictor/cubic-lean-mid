import CubicTenVariables.RationalConeComponents
import HessianTheorem11.UnconditionalFiberDimension
import HessianTheorem11.ReducedTangentRank

/-!
# Dimensions of fibers inside the actual generic-rank source-open

Every component of the closure of an open fiber contains an actual point
of that fiber, by componentwise density. At such a point its actual tangent
lies in the kernel of the polynomial differential restricted to the source
tangent. The proved generic-rank and smooth-tangent formulas and rank-nullity
bound its dimension. The existing lower fiber inequality then gives equality
for nonempty fibers of this source-open.

This does not assert an upper bound on fibers in the excluded closed subset,
nor generic equality for the entire closed source, nor semicontinuity.
-/

noncomputable section
namespace CubicTenVariables.GenericOpenFiberDimension

open MvPolynomial HessianTheorem11 Module

/-- Differentiating the literal constant-image equations, together with
all equations of the containing source, gives actual tangent containment. -/
theorem tangent_le_restricted_fiber_kernel {n m : ℕ}
    (P : Fin m → GeometricPolynomial n) (Y K : Set (GeometricPoint n))
    (v : GeometricPoint m) (hKY : K ⊆ Y)
    (hPv : ∀ z ∈ K, polynomialMap P z = v) (x : GeometricPoint n) :
    affineTangentSpace K x ≤ affineTangentSpace Y x ⊓
      LinearMap.ker (polynomialMapDifferential P x) := by
  intro w hw
  refine ⟨mem_affineTangentSpace.mpr (fun f hf =>
    mem_affineTangentSpace.mp hw f (vanishingIdeal_anti_mono hKY hf)), ?_⟩
  apply LinearMap.mem_ker.mpr
  ext i
  have hf : P i - C (v i) ∈ vanishingIdeal GeometricField K := by
    intro z hz
    change eval z (P i - C (v i)) = 0
    simp only [map_sub, eval_C]
    exact sub_eq_zero.mpr (congrFun (hPv z hz) i)
  have hd := mem_affineTangentSpace.mp hw _ hf
  change polynomialDifferential (P i) x w = 0
  simpa only [polynomialDifferential_apply, map_sub, pderiv_C, sub_zero] using hd

/-- A subspace of the source tangent killed by the differential cannot
have dimension greater than the nullity of that restricted differential. -/
theorem finrank_le_restricted_kernel {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] W) (S T : Submodule K V)
    (hS : S ≤ T ⊓ LinearMap.ker A) :
    finrank K S ≤ finrank K (LinearMap.ker (A.domRestrict T)) := by
  let J : S →ₗ[K] LinearMap.ker (A.domRestrict T) :=
    { toFun := fun w => ⟨⟨w.val, (hS w.property).1⟩, (hS w.property).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearMap.finrank_le_finrank_of_injective (f := J)
  intro u w h
  exact Subtype.ext (congrArg (fun z : LinearMap.ker (A.domRestrict T) => z.val.val) h)

/-- The literal open fiber has the expected upper bound for every
geometric target point, with the empty fiber assigned dimension bottom. -/
theorem generic_open_fiber_dimension_le {n m a b : ℕ}
    {Y : Set (GeometricPoint n)} (hY : AlgebraicallyClosedSet Y)
    {P : Fin m → GeometricPolynomial n}
    {M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField}
    (G : GenericRankOpen Y P M) (v : GeometricPoint m) :
    affineDimension {y | y ∈ G.openSet ∧ polynomialMap P y = v} ≤
      ((G.baseDimension - G.imageDimension : ℕ) : Dimension) := by
  let A := {y | y ∈ G.openSet ∧ polynomialMap P y = v}
  by_cases hne : A.Nonempty
  · let H := geometricClosure A
    have hH : AlgebraicallyClosedSet H := algebraicallyClosedSet_geometricClosure _
    have hHne : H.Nonempty := hne.mono (subset_geometricClosure A)
    obtain ⟨K, hK, hdimK⟩ := ReducedMaximalComponent.maximal_dimension_component H hH hHne
    have hdense : geometricClosure (A ∩ K) = K :=
      RationalConeComponents.closure_inter_component_of_dense H A K hH rfl hK
    have hnAK : (A ∩ K).Nonempty := by
      by_contra hn
      have he : A ∩ K = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      rw [he] at hdense
      have hKempty : K = ∅ := by
        simpa only [geometricClosure, vanishingIdeal_empty, zeroLocus_top] using hdense.symm
      exact hK.irreducible.nonempty.ne_empty hKempty
    obtain ⟨x, hxA, hxK⟩ := hnAK
    have hHY : H ⊆ Y := geometricClosure_subset_closed
      (fun y hy => G.subset hy.1) hY
    have hconst : ∀ z ∈ H, polynomialMap P z = v := by
      intro z hz
      ext i
      have hf : P i - C (v i) ∈ vanishingIdeal GeometricField A := by
        intro y hy
        change eval y (P i - C (v i)) = 0
        simp only [map_sub, eval_C]
        exact sub_eq_zero.mpr (congrFun hy.2 i)
      have he := hz _ hf
      change eval z (P i - C (v i)) = 0 at he
      simpa only [map_sub, eval_C, sub_eq_zero] using he
    have hTK := tangent_le_restricted_fiber_kernel P Y K v
      (hK.subset.trans hHY) (fun z hz => hconst z (hK.subset hz)) x
    have hfin := finrank_le_restricted_kernel (polynomialMapDifferential P x)
      (affineTangentSpace K x) (affineTangentSpace Y x) hTK
    have hr := ((polynomialMapDifferential P x).domRestrict
      (affineTangentSpace Y x)).finrank_range_add_finrank_ker
    rw [G.differential_rank x hxA.1, G.smooth x hxA.1] at hr
    have hupper : finrank GeometricField (affineTangentSpace K x) ≤
        G.baseDimension - G.imageDimension :=
      hfin.trans_eq (Nat.eq_sub_of_add_eq' hr)
    obtain ⟨GK⟩ := Unconditional.genericRankOpen.choose K hK.closed hK.irreducible
      (fun _ : Fin 0 => 0)
      (0 : GeometricPoint n →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
    have hlow := ReducedTangentRank.tangent_dimension_lower_bound GK x hxK
    have hdim : affineDimension K ≤
        ((G.baseDimension - G.imageDimension : ℕ) : Dimension) :=
      hlow.trans (by exact_mod_cast hupper)
    change affineDimension A ≤ _
    rw [hdimK, show H = geometricClosure A from rfl, affineDimension_closure] at hdim
    exact hdim
  · change affineDimension A ≤ _
    rw [Set.not_nonempty_iff_eq_empty.mp hne, affineDimension_empty]
    exact bot_le

/-- The existing pointwise lower fiber inequality gives equality for
nonempty fibers of the actual generic-rank source-open. No generic fiber
equality or semicontinuity statement is assumed. -/
theorem generic_open_fiber_dimension_eq_of_nonempty {n m a b : ℕ}
    {Y : Set (GeometricPoint n)} (hY : AlgebraicallyClosedSet Y)
    (hiY : GeometricallyIrreducible Y)
    {P : Fin m → GeometricPolynomial n}
    {M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField}
    (G : GenericRankOpen Y P M) (v : GeometricPoint m)
    (hne : {y | y ∈ G.openSet ∧ polynomialMap P y = v}.Nonempty) :
    affineDimension {y | y ∈ G.openSet ∧ polynomialMap P y = v} =
      ((G.baseDimension - G.imageDimension : ℕ) : Dimension) := by
  have hupper := generic_open_fiber_dimension_le hY G v
  obtain ⟨k, hk⟩ := ReducedComponentDimension.finite_dimension _ hne
  obtain ⟨x, hx, hxv⟩ := hne
  have hlow := UnconditionalFiberDimension.open_fiber_dimension P Y G.openSet
    hY hiY G.isOpen x hx
  have himage : affineDimension (polynomialMap P '' Y) =
      (G.imageDimension : Dimension) :=
    (affineDimension_closure _).symm.trans G.dimension_image
  rw [hxv, G.dimension_base, himage, hk] at hlow
  rw [hk] at hupper ⊢
  have hu : k ≤ G.baseDimension - G.imageDimension := by exact_mod_cast hupper
  have hl : G.baseDimension ≤ G.imageDimension + k := by exact_mod_cast hlow
  congr 1
  omega

/-- Intersecting the generic-rank open with any further relative
source-open preserves the dimension of each remaining nonempty fiber.
This applies directly to a contact open inside the generic-rank open. -/
theorem subopen_fiber_dimension_eq_of_nonempty {n m a b : ℕ}
    {Y : Set (GeometricPoint n)} (hY : AlgebraicallyClosedSet Y)
    (hiY : GeometricallyIrreducible Y)
    {P : Fin m → GeometricPolynomial n}
    {M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField}
    (G : GenericRankOpen Y P M) (U : Set (GeometricPoint n))
    (hU : RelativelyOpenSet Y U) (hUG : U ⊆ G.openSet)
    (v : GeometricPoint m) (hne : {y | y ∈ U ∧ polynomialMap P y = v}.Nonempty) :
    affineDimension {y | y ∈ U ∧ polynomialMap P y = v} =
      ((G.baseDimension - G.imageDimension : ℕ) : Dimension) := by
  have hupper := (affineDimension_mono (show
      {y | y ∈ U ∧ polynomialMap P y = v} ⊆
        {y | y ∈ G.openSet ∧ polynomialMap P y = v} from
      fun _ hy => ⟨hUG hy.1, hy.2⟩)).trans (generic_open_fiber_dimension_le hY G v)
  obtain ⟨k, hk⟩ := ReducedComponentDimension.finite_dimension _ hne
  obtain ⟨x, hx, hxv⟩ := hne
  have hlow := UnconditionalFiberDimension.open_fiber_dimension P Y U hY hiY hU x hx
  have himage : affineDimension (polynomialMap P '' Y) =
      (G.imageDimension : Dimension) :=
    (affineDimension_closure _).symm.trans G.dimension_image
  rw [hxv, G.dimension_base, himage, hk] at hlow
  rw [hk] at hupper ⊢
  have hu : k ≤ G.baseDimension - G.imageDimension := by exact_mod_cast hupper
  have hl : G.baseDimension ≤ G.imageDimension + k := by exact_mod_cast hlow
  congr 1
  omega

end CubicTenVariables.GenericOpenFiberDimension
