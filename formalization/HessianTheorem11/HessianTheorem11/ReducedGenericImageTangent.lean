import HessianTheorem11.GenericImageTangent
import HessianTheorem11.ReducedTangentRank

/-! Generic image tangent equality from the retained generic-rank theorem.
The actual polynomial chain rule gives containment. Smoothness of the image
and generic rank give equality of dimensions on one common dense open.
No generic-image-tangent or new geometric input is assumed. -/

noncomputable section
namespace HessianTheorem11.ReducedGenericImageTangent
open MvPolynomial Module ReducedTangentRank

@[simp] theorem differential_C {n : ℕ} (c : GeometricField)
    (x v : GeometricPoint n) : polynomialDifferential (C c) x v = 0 := by
  simp [polynomialDifferential_apply]

@[simp] theorem differential_X {n : ℕ} (i : Fin n)
    (x v : GeometricPoint n) : polynomialDifferential (X i) x v = v i := by
  classical
  simp [polynomialDifferential_apply, Pi.single_apply]

/-- The chain rule for the actual evaluation-defined polynomial map. -/
theorem differential_aeval {n m : ℕ} (P : Fin m → GeometricPolynomial n)
    (Q : GeometricPolynomial m) (x v : GeometricPoint n) :
    polynomialDifferential (aeval P Q) x v =
      polynomialDifferential Q (polynomialMap P x) (polynomialMapDifferential P x v) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, differential_add, hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, aeval_X, differential_mul, hf, differential_X, eval_X]
    rw [← eval_polynomialMap]
    rfl

/-- Polynomial differentiation maps the full embedded tangent space into
the tangent space of the actual image closure. -/
theorem range_differential_le_image_tangent {n m : ℕ}
    (P : Fin m → GeometricPolynomial n) (Z : Set (GeometricPoint n))
    (x : GeometricPoint n) :
    LinearMap.range ((polynomialMapDifferential P x).domRestrict
      (affineTangentSpace Z x)) ≤
      affineTangentSpace (geometricClosure (polynomialMap P '' Z)) (polynomialMap P x) := by
  rintro v ⟨u, rfl⟩
  apply mem_affineTangentSpace.mpr
  intro Q hQ
  rw [vanishingIdeal_geometricClosure, vanishingIdeal_polynomialMap_image] at hQ
  have h := mem_affineTangentSpace.mp u.property (aeval P Q) hQ
  exact (differential_aeval P Q x u).symm.trans h

/-- The same chain rule with any actual target containing the image. -/
theorem differential_maps_tangent {n m : ℕ}
    (P : Fin m → GeometricPolynomial n) (Z : Set (GeometricPoint n))
    (U : Set (GeometricPoint m)) (hmap : polynomialMap P '' Z ⊆ U)
    (x v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x) :
    polynomialMapDifferential P x v ∈ affineTangentSpace U (polynomialMap P x) := by
  apply mem_affineTangentSpace.mpr
  intro Q hQ
  have hvan : aeval P Q ∈ vanishingIdeal GeometricField Z := by
    intro z hz
    change eval z (aeval P Q) = 0
    rw [← eval_polynomialMap]
    exact hQ _ (hmap ⟨z, hz, rfl⟩)
  exact (differential_aeval P Q x v).symm.trans
    (mem_affineTangentSpace.mp hv _ hvan)

theorem closed_polynomial_preimage {n m : ℕ}
    (P : Fin m → GeometricPolynomial n) {C : Set (GeometricPoint m)}
    (hC : AlgebraicallyClosedSet C) :
    AlgebraicallyClosedSet (polynomialMap P ⁻¹' C) := by
  apply le_antisymm
  · intro x hx
    have h := polynomialMap_image_closure_subset P (polynomialMap P ⁻¹' C)
      (Set.mem_image_of_mem (polynomialMap P) hx)
    exact geometricClosure_subset_closed (Set.image_preimage_subset _ _) hC h
  · exact subset_geometricClosure _

theorem relativelyOpen_polynomial_preimage {n m : ℕ}
    (P : Fin m → GeometricPolynomial n) (Z : Set (GeometricPoint n))
    {Y O : Set (GeometricPoint m)} (hO : RelativelyOpenSet Y O)
    (hmap : polynomialMap P '' Z ⊆ Y) :
    RelativelyOpenSet Z (Z ∩ polynomialMap P ⁻¹' O) := by
  obtain ⟨C, hC, rfl⟩ := hO
  refine ⟨polynomialMap P ⁻¹' C, closed_polynomial_preimage P hC, ?_⟩
  ext x
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · exact fun h => ⟨h.1, hmap ⟨x, h.1, rfl⟩, h.2⟩

/-- A dense image meets every nonempty open subset of its closure. -/
theorem polynomial_preimage_open_nonempty {n m : ℕ}
    (P : Fin m → GeometricPolynomial n) (Z : Set (GeometricPoint n))
    {O : Set (GeometricPoint m)}
    (hO : RelativelyOpenSet (geometricClosure (polynomialMap P '' Z)) O)
    (hne : O.Nonempty) : (Z ∩ polynomialMap P ⁻¹' O).Nonempty := by
  obtain ⟨C, hC, rfl⟩ := hO
  obtain ⟨y, hy, hyC⟩ := hne
  by_contra hn
  have hsub : polynomialMap P '' Z ⊆ C := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hxc
    exact hn ⟨x, hx, subset_geometricClosure _ ⟨x, hx, rfl⟩, hxc⟩
  exact hyC (geometricClosure_subset_closed hsub hC hy)

theorem dense_inter_open_nonempty {n : ℕ}
    {Z A B : Set (GeometricPoint n)} (hA : geometricClosure A = Z)
    (hB : RelativelyOpenSet Z B) (hne : B.Nonempty) : (A ∩ B).Nonempty := by
  obtain ⟨C, hC, rfl⟩ := hB
  exact dense_open_inter_complement_nonempty hA hC (by
    intro h
    obtain ⟨x, hx, hxc⟩ := hne
    exact hxc (h hx))

/-- The exact former GI interface, constructed from GR alone. -/
def genericImageTangentInput (GR : GenericRankOpenInput) : GenericImageTangentInput where
  choose := by
    intro n m Z hZ hirred P W hW hdW
    let zeroPencil : GeometricPoint n →ₗ[GeometricField]
        Matrix (Fin 0) (Fin 0) GeometricField := 0
    obtain ⟨G⟩ := GR.choose Z hZ hirred P zeroPencil
    let Y := geometricClosure (polynomialMap P '' Z)
    have hY : AlgebraicallyClosedSet Y := algebraicallyClosedSet_geometricClosure _
    have hiY : GeometricallyIrreducible Y :=
      (geometricallyIrreducible_closure_iff _).mpr (hirred.polynomialMap_image P)
    obtain ⟨H⟩ := GR.choose Y hY hiY (fun _ : Fin 0 => 0)
      (0 : GeometricPoint m →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
    let V := Z ∩ polynomialMap P ⁻¹' H.openSet
    have hoV : RelativelyOpenSet Z V := relativelyOpen_polynomial_preimage P Z H.isOpen
      (subset_geometricClosure _)
    have hnV : V.Nonempty := polynomial_preimage_open_nonempty P Z H.isOpen H.nonempty
    have hnGW : (G.openSet ∩ W).Nonempty := by
      simpa only [Set.inter_comm] using dense_inter_open_nonempty hdW G.isOpen G.nonempty
    have hoGW : RelativelyOpenSet Z (G.openSet ∩ W) := G.isOpen.inter hW
    have hdGW := hoGW.dense_of_nonempty hZ hirred hnGW
    let O := (G.openSet ∩ W) ∩ V
    have ho : RelativelyOpenSet Z O := hoGW.inter hoV
    have hn : O.Nonempty := dense_inter_open_nonempty hdGW hoV hnV
    refine ⟨{
      openSet := O
      isOpen := ho
      subset := fun _ hx => hx.1.2
      dense := ho.dense_of_nonempty hZ hirred hn
      nonempty := hn
      image_tangent := ?_ }⟩
    intro x hx
    apply (Submodule.eq_of_le_of_finrank_eq
      (range_differential_le_image_tangent P Z x) ?_).symm
    rw [G.differential_rank x hx.1.1, H.smooth _ hx.2.2]
    have he := G.dimension_image.symm.trans H.dimension_base
    exact_mod_cast he

end HessianTheorem11.ReducedGenericImageTangent
