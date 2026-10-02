import HessianTheorem11.ReducedTangentRank
import HessianTheorem11.PolynomialRestriction

/-! The kernel-bundle tangent-image interface is derived from the retained
generic-rank and kernel-bundle dimension theorems. All tangent equations and
linear identifications below are proved for arbitrary rectangular pencils. -/

noncomputable section
set_option maxHeartbeats 2000000
namespace HessianTheorem11.ReducedKernelTangent
open MvPolynomial Module TangentBundleLinearAlgebra ReducedTangentRank

theorem incidenceTangent_finrank_le {K V E W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup W] [Module K W]
    (H : E →ₗ[K] W) (A : V →ₗ[K] W) (T : Submodule K V) :
    finrank K (incidenceTangent H A T) ≤
      finrank K T + finrank K (LinearMap.ker H) := by
  let S := incidenceTangent H A T
  let f : S →ₗ[K] T :=
    { toFun := fun p => ⟨p.val.1, p.property.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let g : LinearMap.ker f →ₗ[K] LinearMap.ker H :=
    { toFun := fun p => ⟨p.val.val.2, by
        have hp := p.val.property.2
        change H p.val.val.2 + A p.val.val.1 = 0 at hp
        have hz : p.val.val.1 = 0 := congrArg Subtype.val p.property
        change H p.val.val.2 = 0
        simpa only [hz, map_zero, add_zero] using hp⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hg : Function.Injective g := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hp : p.val.val.1 = 0 := congrArg Subtype.val p.property
      have hq : q.val.val.1 = 0 := congrArg Subtype.val q.property
      exact hp.trans hq.symm
    · exact congrArg Subtype.val h
  have hk := LinearMap.finrank_le_finrank_of_injective (f := g) hg
  have hr := Submodule.finrank_le (LinearMap.range f)
  have hd := f.finrank_range_add_finrank_ker
  change finrank K S ≤ _
  omega

theorem differential_restrict {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) GeometricField)
    (p : GeometricPolynomial n) (x v : GeometricPoint m) :
    polynomialDifferential (PolynomialRestriction.restrict B p) x v =
      polynomialDifferential p (B.mulVec x) (B.mulVec v) := by
  simp only [polynomialDifferential_apply, PolynomialRestriction.pderiv_restrict,
    map_sum, map_mul, PolynomialRestriction.eval_restrict, eval_C,
    Finset.sum_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def pullback {n m : ℕ} (L : GeometricPoint m →ₗ[GeometricField] GeometricPoint n)
    (p : GeometricPolynomial n) : GeometricPolynomial m :=
  PolynomialRestriction.restrict (LinearMap.toMatrix' L) p

@[simp] theorem eval_pullback {n m : ℕ}
    (L : GeometricPoint m →ₗ[GeometricField] GeometricPoint n)
    (p : GeometricPolynomial n) (x : GeometricPoint m) :
    eval x (pullback L p) = eval (L x) p := by
  simp [pullback, LinearMap.toMatrix'_mulVec]

@[simp] theorem differential_pullback {n m : ℕ}
    (L : GeometricPoint m →ₗ[GeometricField] GeometricPoint n)
    (p : GeometricPolynomial n) (x v : GeometricPoint m) :
    polynomialDifferential (pullback L p) x v = polynomialDifferential p (L x) (L v) := by
  simp [pullback, differential_restrict, LinearMap.toMatrix'_mulVec]

@[simp] theorem differential_linearCoordinates {n m : ℕ}
    (L : GeometricPoint n →ₗ[GeometricField] GeometricPoint m) (x : GeometricPoint n) :
    polynomialMapDifferential (linearCoordinatePolynomials L) x = L := by
  apply LinearMap.ext
  intro v
  funext i
  change polynomialDifferential (linearCoordinatePolynomials L i) x v = L v i
  change polynomialDifferential
    (PolynomialRestriction.linearForms
      (fun i j => L ((Pi.basisFun GeometricField (Fin n)) j) i) i) x v = L v i
  rw [polynomialDifferential_apply]
  simp only [PolynomialRestriction.pderiv_linearForms, eval_C]
  have h := congrArg (fun z => L z i) ((Pi.basisFun GeometricField (Fin n)).sum_repr v)
  simpa [mul_comm] using h

def pairCoordinateEquiv (n b : ℕ) : PairPoint n b ≃ₗ[GeometricField] GeometricPoint (n+b) :=
  LinearEquiv.piCongrLeft GeometricField (fun _ => GeometricField) finSumFinEquiv

def splitEquiv (n b : ℕ) : GeometricPoint (n+b) ≃ₗ[GeometricField]
    (GeometricPoint n × GeometricPoint b) :=
  (pairCoordinateEquiv n b).symm.trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin b) GeometricField GeometricField)

def baseProjection (n b : ℕ) :
    GeometricPoint (n+b) →ₗ[GeometricField] GeometricPoint n :=
  (LinearMap.fst GeometricField (GeometricPoint n) (GeometricPoint b)).comp
    (splitEquiv n b).toLinearMap

def fiberProjection (n b : ℕ) :
    GeometricPoint (n+b) →ₗ[GeometricField] GeometricPoint b :=
  (LinearMap.snd GeometricField (GeometricPoint n) (GeometricPoint b)).comp
    (splitEquiv n b).toLinearMap

@[simp] theorem baseProjection_pair {n b : ℕ} (p : PairPoint n b) :
    baseProjection n b (pairCoordinateEquiv n b p) = pairLeft p := by
  simp [baseProjection, splitEquiv, pairLeft]
  rfl

@[simp] theorem fiberProjection_pair {n b : ℕ} (p : PairPoint n b) :
    fiberProjection n b (pairCoordinateEquiv n b p) = pairRight p := by
  simp [fiberProjection, splitEquiv, pairRight]
  rfl

def linearPolynomial {n : ℕ} (L : GeometricPoint n →ₗ[GeometricField] GeometricField) :
    GeometricPolynomial n :=
  linearCoordinatePolynomials (LinearMap.pi (fun _ : Fin 1 => L)) 0

@[simp] theorem eval_linearPolynomial {n : ℕ}
    (L : GeometricPoint n →ₗ[GeometricField] GeometricField) (x : GeometricPoint n) :
    eval x (linearPolynomial L) = L x := by
  exact congrFun (polynomialMap_linearCoordinatePolynomials
    (LinearMap.pi (fun _ : Fin 1 => L)) x) 0

@[simp] theorem differential_linearPolynomial {n : ℕ}
    (L : GeometricPoint n →ₗ[GeometricField] GeometricField) (x v : GeometricPoint n) :
    polynomialDifferential (linearPolynomial L) x v = L v := by
  exact congrFun (LinearMap.congr_fun
    (differential_linearCoordinates (LinearMap.pi (fun _ : Fin 1 => L)) x) v) 0

def entryMap {n a b : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (i : Fin a) (j : Fin b) : GeometricPoint n →ₗ[GeometricField] GeometricField :=
  (LinearMap.proj j).comp ((LinearMap.proj i).comp M)

def kernelEquation {n a b : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (i : Fin a) : GeometricPolynomial (n+b) :=
  ∑ j, linearPolynomial ((entryMap M i j).comp (baseProjection n b)) *
    linearPolynomial ((LinearMap.proj j).comp (fiberProjection n b))

@[simp] theorem eval_kernelEquation {n a b : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (i : Fin a) (z : GeometricPoint (n+b)) :
    eval z (kernelEquation M i) =
      (M (baseProjection n b z)).mulVec (fiberProjection n b z) i := by
  simp only [kernelEquation, map_sum, map_mul, eval_linearPolynomial,
    LinearMap.comp_apply, entryMap, LinearMap.proj_apply, Matrix.mulVec, dotProduct]
  rfl

theorem differential_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → GeometricPolynomial n) (x v : GeometricPoint n) :
    polynomialDifferential (∑ i ∈ s, f i) x v =
      ∑ i ∈ s, polynomialDifferential (f i) x v := by
  simp only [polynomialDifferential_apply, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

@[simp] theorem differential_kernelEquation {n a b : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (i : Fin a) (z u : GeometricPoint (n+b)) :
    polynomialDifferential (kernelEquation M i) z u =
      ((M (baseProjection n b z)).mulVec (fiberProjection n b u) +
        (M (baseProjection n b u)).mulVec (fiberProjection n b z)) i := by
  rw [kernelEquation, differential_sum]
  simp only [differential_mul, eval_linearPolynomial, differential_linearPolynomial,
    LinearMap.comp_apply, LinearMap.proj_apply, entryMap, Matrix.mulVec,
    dotProduct, Pi.add_apply, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

def coordinateBundleClosure {n a b : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (O : Set (GeometricPoint n)) : Set (GeometricPoint (n+b)) :=
  geometricClosure (pairCoordinateEquiv n b '' kernelBundle M O)

/-- Differentiating the actual pullbacks and bilinear kernel equations. -/
theorem tangent_bundle_contained {n a b : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (U O : Set (GeometricPoint n)) (hOU : O ⊆ U)
    (x : GeometricPoint n) (v : GeometricPoint b) :
    (affineTangentSpace (coordinateBundleClosure M O)
      (pairCoordinateEquiv n b (pairPoint x v))).map (splitEquiv n b).toLinearMap ≤
    incidenceTangent (M x).mulVecLin (pencilVariation M v) (affineTangentSpace U x) := by
  intro p hp
  obtain ⟨u, hu, rfl⟩ := hp
  rw [mem_incidenceTangent_iff]
  constructor
  · apply mem_affineTangentSpace.mpr
    intro f hf
    have hvan : pullback (baseProjection n b) f ∈
        vanishingIdeal GeometricField (coordinateBundleClosure M O) := by
      rw [coordinateBundleClosure, vanishingIdeal_geometricClosure]
      rintro y ⟨q, hq, rfl⟩
      change eval (pairCoordinateEquiv n b q) (pullback (baseProjection n b) f) = 0
      rw [eval_pullback, baseProjection_pair]
      exact hf (pairLeft q) (hOU hq.1)
    have h := mem_affineTangentSpace.mp hu _ hvan
    rw [differential_pullback, baseProjection_pair, pairLeft_pairPoint] at h
    exact h
  · have he (i : Fin a) : kernelEquation M i ∈
        vanishingIdeal GeometricField (coordinateBundleClosure M O) := by
      rw [coordinateBundleClosure, vanishingIdeal_geometricClosure]
      rintro y ⟨q, hq, rfl⟩
      change eval (pairCoordinateEquiv n b q) (kernelEquation M i) = 0
      rw [eval_kernelEquation, baseProjection_pair, fiberProjection_pair]
      exact congrFun hq.2 i
    ext i
    have h := mem_affineTangentSpace.mp hu _ (he i)
    rw [differential_kernelEquation, baseProjection_pair, fiberProjection_pair,
      pairLeft_pairPoint, pairRight_pairPoint] at h
    exact h

/-- Fully proved replacement for KB. The only retained input used is AG:
generic differential rank and the dimension/irreducibility of constant-rank
kernel bundles. -/
def kernelBundleTangentImageInput (AG : ConcentrationGeometryInput) :
    KernelBundleTangentImageInput where
  dimension_lower_bound := by
    intro n a b M U O hU hirred hO hdense ell hell x hx hsmooth v hv
    have hOU : O ⊆ U := by
      obtain ⟨C, _, rfl⟩ := hO
      exact Set.diff_subset
    let E := pairCoordinateEquiv n b
    let PE := PolynomialCoordinateEquiv.ofLinearEquiv E
    let Y := coordinateBundleClosure M O
    let z := E (pairPoint x v)
    let t := finrank GeometricField (affineTangentSpace U x)
    let TY := affineTangentSpace Y z
    let S := incidenceTangent (M x).mulVecLin (pencilVariation M v) (affineTangentSpace U x)
    have hyclosed : AlgebraicallyClosedSet Y := algebraicallyClosedSet_geometricClosure _
    have hyirred : GeometricallyIrreducible Y := by
      apply (geometricallyIrreducible_closure_iff _).mpr
      have hb := AG.closure_irreducible M U O hU hirred hO hdense ell hell
      have hb' := (geometricallyIrreducible_closure_iff _).mp hb
      have he := hb'.polynomialMap_image PE.forward
      change GeometricallyIrreducible (PE.forwardMap '' kernelBundle M O) at he
      simpa only [PE, E, PolynomialCoordinateEquiv.ofLinearEquiv_forwardMap] using he
    have hydim : affineDimension Y = ((t + ell : ℕ) : Dimension) := by
      rw [show Y = geometricClosure (E '' kernelBundle M O) from rfl, affineDimension_closure]
      have he := PE.affineDimension_image (kernelBundle M O)
      simp only [PE, PolynomialCoordinateEquiv.ofLinearEquiv_forwardMap] at he
      rw [he]
      exact AG.dimension M U O hU hirred hO hdense t ell hsmooth hell
    have hz : z ∈ Y := by
      apply subset_geometricClosure
      exact ⟨pairPoint x v, ⟨hx, hv⟩, rfl⟩
    let P := linearCoordinatePolynomials (fiberProjection n b)
    obtain ⟨G⟩ := AG.choose Y hyclosed hyirred P
      (0 : GeometricPoint (n+b) →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
    have hlow := tangent_dimension_lower_bound G z hz
    rw [hydim] at hlow
    have hlow' : t + ell ≤ finrank GeometricField TY := by exact_mod_cast hlow
    have hcontained : TY.map (splitEquiv n b).toLinearMap ≤ S :=
      tangent_bundle_contained M U O hOU x v
    have hmapdim : finrank GeometricField (TY.map (splitEquiv n b).toLinearMap) =
        finrank GeometricField TY := (splitEquiv n b).finrank_map_eq TY
    have hupper := incidenceTangent_finrank_le (M x).mulVecLin
      (pencilVariation M v) (affineTangentSpace U x)
    rw [hell x hx] at hupper
    have hmono := Submodule.finrank_mono hcontained
    rw [hmapdim] at hmono
    have hdimTY : finrank GeometricField TY = t + ell := by
      exact le_antisymm (hmono.trans hupper) hlow'
    have heq : TY.map (splitEquiv n b).toLinearMap = S := by
      apply Submodule.eq_of_le_of_finrank_eq hcontained
      rw [hmapdim]
      exact le_antisymm hmono (hupper.trans_eq hdimTY.symm)
    have hysmooth : affineDimension Y = (finrank GeometricField TY : Dimension) := by
      rw [hydim, hdimTY]
    have hbound := differential_rank_le_image_dimension G z hz hysmooth
    have hder : polynomialMapDifferential P z = fiberProjection n b :=
      differential_linearCoordinates (fiberProjection n b) z
    have hrange : LinearMap.range (tangentProjection (M x).mulVecLin
        (pencilVariation M v) (affineTangentSpace U x)) =
        LinearMap.range ((fiberProjection n b).domRestrict TY) := by
      rw [tangentProjection, LinearMap.range_domRestrict]
      change S.map (LinearMap.snd GeometricField (GeometricPoint n) (GeometricPoint b)) = _
      rw [← heq, LinearMap.range_domRestrict]
      ext w
      constructor
      · rintro ⟨p, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨u, hu, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨splitEquiv n b u, ⟨u, hu, rfl⟩, rfl⟩
    have himage : geometricClosure (polynomialMap P '' Y) =
        geometricClosure (pairRight '' kernelBundle M O) := by
      change geometricClosure (polynomialMap P '' geometricClosure (E '' kernelBundle M O)) = _
      rw [geometricClosure_polynomialMap_image_closure]
      congr 1
      simp only [P, polynomialMap_linearCoordinatePolynomials, Set.image_image]
      congr 1
      funext q
      exact fiberProjection_pair q
    rw [hder, himage] at hbound
    rw [hrange]
    exact hbound

end HessianTheorem11.ReducedKernelTangent
