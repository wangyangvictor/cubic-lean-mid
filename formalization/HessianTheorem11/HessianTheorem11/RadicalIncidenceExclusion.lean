import HessianTheorem11.CubicRadicalOpen
import HessianTheorem11.RankClosure
import HessianTheorem11.SingularCubicZeroKernel
import HessianTheorem11.SingularRadialEquality
import HessianTheorem11.ConePointSelection

/-! The radical-incidence dimension argument for the eleven-variable
corank-two exception. Its line-fiber and rank-four premises concern the
actual intrinsic radical and are discharged by local normal-form algebra.
Only the general bundle/fiber/linear-section inputs are external geometry. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

/-- A line in one intrinsic radical supplies a nonzero point in the actual
second image. -/
theorem radicalImage_not_origin {n : ℕ} {F : GeometricPolynomial n}
    (O : CubicRadicalOpen F) (hline : O.nullity = 1) :
    ¬ geometricClosure (radicalImage F O.openSet) ⊆ {0} := by
  obtain ⟨x, hx⟩ := O.nonempty
  have hd : 0 < finrank GeometricField (intrinsicRadical F x) := by
    rw [O.dimension_kernel x hx, hline]
    norm_num
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hd
  have hv0 : (v : GeometricPoint n) ≠ 0 := by
    intro h
    apply hv
    exact Subtype.ext h
  have hmem : (v : GeometricPoint n) ∈ radicalImage F O.openSet :=
    ⟨Sum.elim x v, ⟨hx, v.property⟩, rfl⟩
  intro hsub
  exact hv0 (Set.mem_singleton_iff.mp (hsub (subset_geometricClosure _ hmem)))

theorem radicalImage_irreducible {n : ℕ} {F : GeometricPolynomial n}
    (O : CubicRadicalOpen F) : GeometricallyIrreducible (radicalImage F O.openSet) := by
  have h := O.bundle_irreducible.polynomialMap_image (fun i : Fin n => X (Sum.inr i))
  have he : polynomialMap (fun i : Fin n => X (Sum.inr i)) =
      (fun p : (Fin n ⊕ Fin n) → GeometricField => p ∘ Sum.inr) := by
    ext p i
    simp [polynomialMap]
  rw [he] at h
  exact h

/-- No rank-nine cubic can have the actual radical line family supplied by
its remaining first-normal configuration. -/
theorem eleven_radical_line_exception_impossible
    (MR : GenericMatrixRankInput) (GR : GenericRankOpenInput)
    (GP : GenericConePointSelectionInput) (DT : SymmetricDeterminantalTangentInput)
    (FD : AffineFiberDimensionInput) (LS : LinearSectionDimensionInput)
    (boundary : NonzeroLimitTransport.RationalRelativeBoundaryInput)
    (bigCell : NonzeroLimitTransport.TextbookOrbitBigCellInput)
    (F : AnisotropicCubic 11)
    (hsemi : WeightSemistable (geometricPolynomial F.polynomial))
    (hirred : Irreducible (geometricPolynomial F.polynomial))
    (hdet : hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0)
    (O : CubicRadicalOpen (geometricPolynomial F.polynomial))
    (hline : O.nullity = 1)
    (hrank : ∀ x ∈ O.openSet, ∀ v ∈ intrinsicRadical (geometricPolynomial F.polynomial) x,
      (hessian (geometricPolynomial F.polynomial) v).rank ≤ 4)
    (hgeneric : geometricCubicGenericRank (geometricPolynomial F.polynomial) = 9) : False := by
  classical
  let f := geometricPolynomial F.polynomial
  have hf : f.IsHomogeneous 3 := geometric_homogeneous F.homogeneous
  let Z := geometricClosure (radicalImage f O.openSet)
  have hZclosed : AlgebraicallyClosedSet Z := algebraicallyClosedSet_geometricClosure _
  have hZirred : GeometricallyIrreducible Z :=
    (geometricallyIrreducible_closure_iff _).mpr (radicalImage_irreducible O)
  have hZcone : IsAffineCone Z := (radicalImage_cone f O.openSet).geometricClosure
  have hZnot : ¬ Z ⊆ {0} := radicalImage_not_origin O hline
  have hZsing : ∀ z ∈ Z, gradient f z = 0 := radicalImage_closure_singular hf _
  have hZrank : ∀ z ∈ Z, (hessian f z).rank ≤ 4 := by
    apply polynomialMatrix_rank_le_on_closure MR (radicalImage f O.openSet)
      (radicalImage_irreducible O) (hessianPolynomial f) 4
    rintro z ⟨p, hp, rfl⟩
    exact hrank (p ∘ Sum.inl) hp.1 (p ∘ Sum.inr) hp.2
  let P := GP.choose Z hZclosed hZirred hZcone hZnot (hessianLinearMap f hf)
    (fun i => pderiv i f)
  let T := affineTangentSpace Z P.point
  let t := finrank GeometricField T
  let r := (hessian f P.point).rank
  have htL : T ≤ LinearMap.ker (hessian f P.point).mulVecLin :=
    affineTangentSpace_le_hessian_ker f Z hZsing P.point
  have htensor := hessian_tangent_polarization_zero DT f hf Z P.point P.member P.rank_maximal
  have hrad : t + 3 ≤ 2 * r := singular_radial_of_tensor_vanishing f hf hsemi
    P.point P.nonzero T P.radial htL htensor
  have hr4 : r ≤ 4 := hZrank P.point P.member
  have hrpos : 0 < r := by omega
  obtain ⟨G⟩ := GR.choose Z hZclosed hZirred
    (fun _ : Fin 0 => (0 : GeometricPolynomial 11)) (hessianLinearMap f hf)
  have hGrank : ∀ z ∈ G.openSet, (hessian f z).rank = r := by
    intro z hz
    apply le_antisymm (P.rank_maximal z (G.subset hz))
    exact G.maximal_rank z hz P.point P.member
  have hGnonzero : ∀ z ∈ G.openSet, z ≠ 0 := by
    intro z hz he
    have hh := hGrank z hz
    have hzero : hessian f (0 : GeometricPoint 11) = 0 := (hessianLinearMap f hf).map_zero
    rw [he, hzero, Matrix.rank_zero] at hh
    omega
  have hker_not_zero : ∀ z ∈ G.openSet,
      ∃ u ∈ LinearMap.ker (hessian f z).mulVecLin, eval u f ≠ 0 := by
    intro z hz
    by_contra h
    push_neg at h
    have hb := singular_cubic_zero_kernel_rank_bound f hf hsemi z (hGnonzero z hz)
      (hZsing z (G.subset hz)) h
    rw [hGrank z hz] at hb
    omega
  let π : Fin 11 → MvPolynomial (Fin 11 ⊕ Fin 11) GeometricField := fun i => X (Sum.inr i)
  have hπ (p : PairPoint 11 11) : polynomialMap π p = pairRight p := by
    ext i
    simp [π, polynomialMap, pairRight]
  have himage : geometricClosure (polynomialMap π '' radicalBundle f O.openSet) = Z := by
    congr 1
    exact Set.image_congr (fun p _ => hπ p)
  have hfib : ∀ z ∈ G.openSet,
      affineDimension {p | p ∈ radicalBundle f O.openSet ∧ polynomialMap π p = z} ≤
        ((10 - r : ℕ) : Dimension) := by
    intro z hz
    let L := LinearMap.ker (hessian f z).mulVecLin
    let A := {x : GeometricPoint 11 | x ∈ L ∧ eval x f = 0}
    have hsub : {p | p ∈ radicalBundle f O.openSet ∧ polynomialMap π p = z} ⊆
        {p : PairPoint 11 11 | pairLeft p ∈ A ∧ pairRight p = z} := by
      rintro p ⟨hp, hpz⟩
      rw [hπ] at hpz
      refine ⟨⟨?_, O.subset hp.1⟩, hpz⟩
      have hk := intrinsicRadical_radial_in_kernel hf hp.2
      change pairLeft p ∈ LinearMap.ker (hessian f (pairRight p)).mulVecLin at hk
      rwa [hpz] at hk
    have hdL : finrank GeometricField L = 11 - r := by
      have hd := (hessian f z).mulVecLin.finrank_range_add_finrank_ker
      change (hessian f z).rank + finrank GeometricField L = finrank GeometricField (GeometricPoint 11) at hd
      simp only [GeometricPoint, Module.finrank_pi, Fintype.card_fin] at hd
      rw [hGrank z hz] at hd
      omega
    calc
      _ ≤ affineDimension {p : PairPoint 11 11 | pairLeft p ∈ A ∧ pairRight p = z} :=
        affineDimension_mono hsub
      _ = affineDimension A := LS.fixed_coordinates A z
      _ ≤ ((finrank GeometricField L - 1 : ℕ) : Dimension) :=
        LS.subspace_hypersurface L f (hker_not_zero z hz)
      _ = ((10 - r : ℕ) : Dimension) := by rw [hdL]; congr 1; omega
  have hdR := FD.dimension_le π (radicalBundle f O.openSet) O.bundle_irreducible
    O.bundle_locally_closed G.openSet (by rw [himage]; exact G.isOpen)
      (by rw [himage]; exact G.dense) (10 - r) hfib
  rw [himage, O.bundle_dimension, hline, P.dimension] at hdR
  have hdim : 11 ≤ t + (10 - r) := by exact_mod_cast hdR
  have hr : r = 4 := by omega
  have ht : t = 5 := by omega
  have hnot := SingularRadialEquality.equality_not_dvd_hessianDeterminant
    boundary bigCell F (by norm_num) hirred hdet P.point P.nonzero T P.radial
    htL htensor ht hr
  apply hnot
  have hm : 0 < O.divisor.multiplicity := by
    have hc := O.divisor.corank_bound
    rw [hgeneric] at hc
    omega
  rw [O.divisor.determinant_factorization]
  exact dvd_mul_of_dvd_left (dvd_pow_self f (Nat.ne_of_gt hm)) _

end HessianTheorem11
