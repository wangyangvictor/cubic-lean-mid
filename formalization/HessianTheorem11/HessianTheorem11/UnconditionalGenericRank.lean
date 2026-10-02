import HessianTheorem11.UnconditionalGenericImageDimension

/-! A zero-input construction of the complete generic smoothness and
polynomial differential-rank package used in the geometry proofs. -/
noncomputable section
namespace HessianTheorem11.UnconditionalGeneric
open MvPolynomial Module ReducedTangentRank

/-- Preserve the actual finite ideal-generation identity alongside its
everywhere-valid tangent-space presentation. -/
def idealTangentPresentation {n c : ℕ} (U : Set (GeometricPoint n))
    (f : Fin c → GeometricPolynomial n)
    (hf : Submodule.span (GeometricPolynomial n) (Set.range f) =
      vanishingIdeal GeometricField U) : TangentPresentation U := by
  have hmem (i) : f i ∈ vanishingIdeal GeometricField U := by
    rw [←hf]
    exact Submodule.subset_span ⟨i,rfl⟩
  refine ⟨c,f,hmem,?_⟩
  intro x hx
  ext v
  constructor
  · intro hv
    apply LinearMap.mem_ker.mpr
    ext i
    exact mem_affineTangentSpace.mp hv (f i) (hmem i)
  · intro hv
    apply mem_affineTangentSpace.mpr
    intro p hp
    rw [←hf] at hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨i,rfl⟩ := hp
      exact congrFun (LinearMap.mem_ker.mp hv) i
    | zero => simp [polynomialDifferential_apply]
    | add p q hp hq ihp ihq => rw [differential_add,ihp,ihq,add_zero]
    | smul a p hp ih =>
      change polynomialDifferential (a*p) x v=0
      have hpU : p ∈ vanishingIdeal GeometricField U := hf ▸ hp
      rw [differential_mul,show eval x p=0 from hpU x hx,ih]
      ring

/-- Generic smoothness, image differential rank, and maximum pencil rank
on one actual dense nonempty open. This constructor has no external input.
Its two dimension identifications are proved using Noether normalization,
Kähler differentials, quotient derivations, and separability in characteristic
zero; the common open is constructed from three actual nonzero minors. -/
def genericRankOpenInput : GenericRankOpenInput where
  choose := by
    intro n m a b U hU hi P M
    letI : (vanishingIdeal GeometricField U).IsPrime := hi
    obtain ⟨c,f,hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian (vanishingIdeal GeometricField U))
    let J := idealTangentPresentation U f hf
    obtain ⟨G⟩ := exists_jacobianOpen U hU hi P M J
    refine ⟨G.toGenericRankOpen ?_ ?_⟩
    · exact generic_jacobian_dimension (vanishingIdeal GeometricField U) f hf
    · change ringKrullDim (affineCoordinateRing
        (vanishingIdeal GeometricField (geometricClosure (polynomialMap P '' U)))) = _
      rw [vanishingIdeal_geometricClosure,vanishingIdeal_polynomialMap_image]
      exact generic_image_dimension (vanishingIdeal GeometricField U) f hf P

end HessianTheorem11.UnconditionalGeneric
