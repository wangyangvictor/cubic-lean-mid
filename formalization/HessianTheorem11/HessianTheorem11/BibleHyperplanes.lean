import HessianTheorem11.CubicRankIrreducibility
import HessianTheorem11.SingularExceptionalComponent
import HessianTheorem11.LinearEmbeddingGeometry
import HessianTheorem11.KernelQuadraticDominance

/-! Hyperplane sections of actual cubic polynomials. The sole additional
dimension input is the general principal-ideal dimension estimate for a
positive homogeneous equation on a closed affine cone. -/

noncomputable section
set_option maxHeartbeats 800000
namespace HessianTheorem11.BibleHyperplanes
open MvPolynomial Module Matrix PolynomialRestriction

/-- The standard projective intersection theorem, expressed on affine cones.
The positive degree forces the equation to vanish at the vertex, preventing
the empty affine intersection exception. No cubic or Hessian occurs here. -/
structure HomogeneousCutDimensionInput : Prop where
  dimension_cut : ∀ {n : ℕ} (Z : Set (GeometricPoint n)),
    AlgebraicallyClosedSet Z → IsAffineCone Z →
    ∀ (P : GeometricPolynomial n) (d : ℕ), 0 < d → P.IsHomogeneous d →
      affineDimension Z ≤ affineDimension {x | x ∈ Z ∧ eval x P = 0} + 1

theorem HomogeneousCutDimensionInput.bound_of_cut
    (HI : HomogeneousCutDimensionInput) {n : ℕ} (Z : Set (GeometricPoint n))
    (hc : AlgebraicallyClosedSet Z) (hcone : IsAffineCone Z)
    (P : GeometricPolynomial n) (d : ℕ) (hd : 0 < d) (hP : P.IsHomogeneous d)
    (b : ℕ) (hb : affineDimension {x | x ∈ Z ∧ eval x P = 0} ≤ (b : Dimension)) :
    affineDimension Z ≤ ((b + 1 : ℕ) : Dimension) := by
  calc
    affineDimension Z ≤ affineDimension {x | x ∈ Z ∧ eval x P = 0} + 1 :=
      HI.dimension_cut Z hc hcone P d hd hP
    _ ≤ (b : Dimension) + 1 := by simpa only [add_comm] using add_le_add_right hb 1
    _ = ((b + 1 : ℕ) : Dimension) := by simp

/-- One ambient coordinate detects the one-dimensional annihilator of a
hyperplane frame. This is linear algebra, with no geometric input. -/
theorem exists_normal_detector {K : Type*} [Field K] {m : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin m) K) (hB : Function.Injective B.mulVec) :
    ∃ j : Fin (m + 1), ∀ v : Fin (m + 1) → K,
      B.transpose.mulVec v = 0 → v j = 0 → v = 0 := by
  let L := LinearMap.ker B.transpose.mulVecLin
  have hr : B.rank = m := by
    change finrank K (LinearMap.range B.mulVecLin) = m
    rw [LinearMap.finrank_range_of_inj hB]
    simp
  have hrT : finrank K (LinearMap.range B.transpose.mulVecLin) = m := by
    change B.transpose.rank = m
    rw [Matrix.rank_transpose, hr]
  have hdim := LinearMap.finrank_range_add_finrank_ker B.transpose.mulVecLin
  have hL : finrank K L = 1 := by
    rw [hrT] at hdim
    simp only [Module.finrank_pi, Fintype.card_fin] at hdim
    change m + finrank K L = m + 1 at hdim
    omega
  obtain ⟨v, hv, hspan⟩ := finrank_eq_one_iff'.mp hL
  have hv' : (v : Fin (m + 1) → K) ≠ 0 := by
    intro h
    apply hv
    exact Subtype.ext h
  obtain ⟨j, hj⟩ : ∃ j, (v : Fin (m + 1) → K) j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv' (funext h)
  refine ⟨j, ?_⟩
  intro w hw hwj
  obtain ⟨a, ha⟩ := hspan ⟨w, hw⟩
  have haj : a * (v : Fin (m + 1) → K) j = 0 := by
    have hh := congrArg (fun z : L => (z : Fin (m + 1) → K) j) ha
    simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hwj] using hh
  have ha0 : a = 0 := (mul_eq_zero.mp haj).resolve_right hj
  have hz : (⟨w, hw⟩ : L) = 0 := by simpa [ha0] using ha.symm
  exact congrArg Subtype.val hz

theorem gradient_restrict {K : Type*} [CommRing K] {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) K) (F : MvPolynomial (Fin n) K) (x : Fin m → K) :
    gradient (restrict B F) x = B.transpose.mulVec (gradient F (B.mulVec x)) := by
  ext j
  simp only [gradient, pderiv_restrict, map_sum, map_mul, eval_C,
    eval_restrict, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem ambient_gradient_zero_of_section_and_normal {m : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin m) GeometricField)
    (F : GeometricPolynomial (m + 1)) (j : Fin (m + 1))
    (hj : ∀ v, B.transpose.mulVec v = 0 → v j = 0 → v = 0)
    (x : GeometricPoint m) (hs : gradient (restrict B F) x = 0)
    (hn : eval x (restrict B (pderiv j F)) = 0) : gradient F (B.mulVec x) = 0 := by
  apply hj
  · rwa [← gradient_restrict]
  · simpa only [eval_restrict, gradient] using hn

def singularCone {n : ℕ} (F : GeometricPolynomial n) : Set (GeometricPoint n) :=
  {x | gradient F x = 0}

theorem singularCone_eq {n : ℕ} (F : GeometricPolynomial n) :
    singularCone F = finiteEquationZeroSet (fun i => pderiv i F) := by
  ext x
  simp only [singularCone, finiteEquationZeroSet, gradient, Set.mem_setOf_eq,
    funext_iff, Pi.zero_apply]

theorem singularCone_closed {n : ℕ} (F : GeometricPolynomial n) :
    AlgebraicallyClosedSet (singularCone F) := by
  rw [singularCone_eq]
  exact finiteEquationZeroSet_closed _

theorem singularCone_cone {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) :
    IsAffineCone (singularCone F) := by
  rw [singularCone_eq]
  exact finiteQuadraticZeroSet_cone _ (fun i => hF.pderiv)

theorem gradient_restrict_zero_iff {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) GeometricField) (F : GeometricPolynomial n)
    (x : GeometricPoint m) :
    gradient (restrict B F) x = 0 ↔
      ∀ v : GeometricPoint m, dotProduct (B.mulVec v) (gradient F (B.mulVec x)) = 0 := by
  rw [gradient_restrict]
  have he (v : GeometricPoint m) :
      dotProduct (B.mulVec v) (gradient F (B.mulVec x)) =
        dotProduct v (B.transpose.mulVec (gradient F (B.mulVec x))) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp_rw [he]
  constructor
  · intro h v
    rw [h, dotProduct_zero]
  · intro h
    ext i
    simpa using h (Pi.single i 1)

/-- The embedded section singular cone is the intrinsic annihilator of the
ambient differential restricted to the actual hyperplane subspace. Thus it
does not depend on the choice of the hyperplane frame. -/
theorem frame_singular_image {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) GeometricField) (F : GeometricPolynomial n) :
    B.mulVec '' singularCone (restrict B F) =
      {x | x ∈ LinearMap.range B.mulVecLin ∧
        ∀ y ∈ LinearMap.range B.mulVecLin, dotProduct y (gradient F x) = 0} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact (gradient_restrict_zero_iff B F u).mp hu v
  · rintro ⟨⟨u, rfl⟩, hu⟩
    refine ⟨u, ?_, rfl⟩
    exact (gradient_restrict_zero_iff B F u).mpr (fun v => hu _ ⟨v, rfl⟩)

theorem homogeneous_cut_closed {n : ℕ} (Z : Set (GeometricPoint n))
    (hc : AlgebraicallyClosedSet Z) (P : GeometricPolynomial n) :
    AlgebraicallyClosedSet {x | x ∈ Z ∧ eval x P = 0} := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨geometricClosure_subset_closed (fun y hy => hy.1) hc hx,
      geometricClosure_subset_of_polynomial_vanishes _ P (fun y hy => hy.2) x hx⟩
  · exact subset_geometricClosure _

theorem homogeneous_cut_cone {n d : ℕ} (Z : Set (GeometricPoint n))
    (hc : IsAffineCone Z) (P : GeometricPolynomial n) (hP : P.IsHomogeneous d) :
    IsAffineCone {x | x ∈ Z ∧ eval x P = 0} := by
  intro a x hx
  refine ⟨hc a x hx.1, ?_⟩
  have he := LocalCubicNormalForm.homogeneous_eval₂_common_scalar P hP
    (RingHom.id GeometricField) x a
  change eval₂ (RingHom.id GeometricField) (fun i => a * x i) P = 0
  rw [he]
  change a ^ d * eval x P = 0
  rw [hx.2, mul_zero]

theorem affineDimension_le_of_image_subset {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) GeometricField) (hB : Function.Injective B.mulVec)
    (Z : Set (GeometricPoint m)) (T : Set (GeometricPoint n))
    (h : ∀ x ∈ Z, B.mulVec x ∈ T) : affineDimension Z ≤ affineDimension T := by
  rw [← affineDimension_linearMap_image B.mulVecLin hB Z]
  exact affineDimension_mono (by rintro y ⟨x, hx, rfl⟩; exact h x hx)

/-- Cutting the section singular cone by one actual normal derivative embeds
it into the ambient singular cone. The dimension loss is at most one. -/
theorem section_singular_dimension_le (HI : HomogeneousCutDimensionInput)
    {m s : ℕ} (B : Matrix (Fin (m + 1)) (Fin m) GeometricField)
    (hB : Function.Injective B.mulVec) (F : GeometricPolynomial (m + 1))
    (hF : F.IsHomogeneous 3) (hs : affineDimension (singularCone F) ≤ (s : Dimension)) :
    affineDimension (singularCone (restrict B F)) ≤ ((s + 1 : ℕ) : Dimension) := by
  obtain ⟨j, hj⟩ := exists_normal_detector B hB
  apply HI.bound_of_cut (singularCone (restrict B F)) (singularCone_closed _)
    (singularCone_cone _ (homogeneous_restrict B F hF))
    (restrict B (pderiv j F)) 2 (by omega)
    (homogeneous_restrict B _ hF.pderiv) s
  apply le_trans (affineDimension_le_of_image_subset B hB _ (singularCone F) ?_) hs
  intro x hx
  exact ambient_gradient_zero_of_section_and_normal B F j hj x hx.1 hx.2

/-- A hyperplane restriction is irreducible whenever three positive
homogeneous cuts cannot fit inside the ambient singular locus. -/
theorem section_irreducible (HI : HomogeneousCutDimensionInput)
    (GR : GenericRankOpenInput) {m s : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin m) GeometricField) (hB : Function.Injective B.mulVec)
    (F : GeometricPolynomial (m + 1)) (hF : F.IsHomogeneous 3)
    (hs : affineDimension (singularCone F) ≤ (s : Dimension)) (hms : s + 3 < m) :
    Irreducible (restrict B F) := by
  obtain ⟨j, hj⟩ := exists_normal_detector B hB
  let N := restrict B (pderiv j F)
  have hN : N.IsHomogeneous 2 := homogeneous_restrict B _ hF.pderiv
  have hu : IsAffineCone (Set.univ : Set (GeometricPoint m)) := by
    intro a x hx; trivial
  have hnonzero : restrict B F ≠ 0 := by
    intro hz
    have hc : affineDimension {x : GeometricPoint m | x ∈ Set.univ ∧ eval x N = 0} ≤
        (s : Dimension) := by
      apply le_trans (affineDimension_le_of_image_subset B hB _ (singularCone F) ?_) hs
      intro x hx
      apply ambient_gradient_zero_of_section_and_normal B F j hj x _ hx.2
      rw [hz]
      ext i
      simp [gradient]
    have hh := HI.bound_of_cut Set.univ algebraicallyClosedSet_univ hu N 2
      (by omega) hN s hc
    rw [affineDimension_univ_from_generic_rank GR m] at hh
    have hh' : m ≤ s + 1 := by exact_mod_cast hh
    omega
  by_contra hred
  obtain ⟨L, Q, hL, hQ, hfac⟩ := reducible_homogeneous_cubic_linear_times_quadratic
    (restrict B F) (homogeneous_restrict B F hF) hnonzero hred
  let Z₁ := {x : GeometricPoint m | x ∈ Set.univ ∧ eval x L = 0}
  let Z₂ := {x : GeometricPoint m | x ∈ Z₁ ∧ eval x Q = 0}
  have hc₁ : AlgebraicallyClosedSet Z₁ := homogeneous_cut_closed _ algebraicallyClosedSet_univ L
  have hc₂ : AlgebraicallyClosedSet Z₂ := homogeneous_cut_closed _ hc₁ Q
  have hcone₁ : IsAffineCone Z₁ := homogeneous_cut_cone _ hu L hL
  have hcone₂ : IsAffineCone Z₂ := homogeneous_cut_cone _ hcone₁ Q hQ
  have hcut : affineDimension {x : GeometricPoint m | x ∈ Z₂ ∧ eval x N = 0} ≤
      (s : Dimension) := by
    apply le_trans (affineDimension_le_of_image_subset B hB _ (singularCone F) ?_) hs
    intro x hx
    apply ambient_gradient_zero_of_section_and_normal B F j hj x _ hx.2
    have hLx : eval x L = 0 := hx.1.1.2
    have hQx : eval x Q = 0 := hx.1.2
    ext i
    simp [gradient, hfac, Derivation.leibniz, hLx, hQx]
  have h₂ := HI.bound_of_cut Z₂ hc₂ hcone₂ N 2 (by omega) hN s hcut
  have h₁ := HI.bound_of_cut Z₁ hc₁ hcone₁ Q 2 (by omega) hQ (s + 1) h₂
  have h₀ := HI.bound_of_cut Set.univ algebraicallyClosedSet_univ hu L 1
    (by omega) hL ((s + 1) + 1) h₁
  rw [affineDimension_univ_from_generic_rank GR m] at h₀
  have hh : m ≤ s + 1 + 1 + 1 := by exact_mod_cast h₀
  omega

end HessianTheorem11.BibleHyperplanes
