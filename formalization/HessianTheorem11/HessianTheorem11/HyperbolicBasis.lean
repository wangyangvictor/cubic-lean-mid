import HessianTheorem11.SimultaneousBasis
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic

/-! Actual hyperbolic splitting with a prescribed isotropic vector. This is
linear algebra used to choose the coordinates in the local cubic calculation. -/

noncomputable section
namespace HessianTheorem11.HyperbolicBasis
open Module Submodule

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V]

theorem exists_partner (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x : V) (hx : B x x = 0) (hxr : x ∉ LinearMap.ker B) :
    ∃ z : V, B x z = 2 ∧ B z z = 0 := by
  have hex : ∃ y, B x y ≠ 0 := by
    by_contra h
    push_neg at h
    apply hxr
    apply LinearMap.ext
    exact h
  obtain ⟨y, hy⟩ := hex
  let u := (2 / B x y) • y
  have hxu : B x u = 2 := by
    simp [u, hy]
  have hux : B u x = 2 := by rw [hB.eq, hxu]
  refine ⟨u - (B u u / 4) • x, ?_, ?_⟩
  · simp [hx, hxu]
  · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      hxu, hux, hx, smul_eq_mul]
    ring

def plane (x z : V) : Submodule K V := span K (Set.range ![x, z])

theorem mem_plane (x z : V) {v : V} :
    v ∈ plane (K := K) x z ↔ ∃ a b : K, a • x + b • z = v := by
  have hr : Set.range ![x,z] = {x,z} := by
    ext v
    simp [or_comm]
  rw [plane, hr, Submodule.mem_span_pair]

theorem x_mem_plane (x z : V) : x ∈ plane (K := K) x z :=
  (mem_plane x z).mpr ⟨1, 0, by simp⟩

theorem z_mem_plane (x z : V) : z ∈ plane (K := K) x z :=
  (mem_plane x z).mpr ⟨0, 1, by simp⟩

theorem pair_independent (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x z : V) (hxx : B x x = 0) (hzz : B z z = 0) (hxz : B x z = 2) :
    LinearIndependent K ![x, z] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hz
    change z = 0 at hz
    have := hxz
    simp [hz] at this
  · intro a ha
    have he := congrArg (fun v => B z v) ha
    have hzx : B z x = 2 := by rw [hB.eq, hxz]
    simpa [hzz, hzx] using he

def planeBasis (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x z : V) (hxx : B x x = 0) (hzz : B z z = 0) (hxz : B x z = 2) :
    Basis (Fin 2) K (plane (K := K) x z) :=
  Basis.span (pair_independent B hB x z hxx hzz hxz)

@[simp] theorem planeBasis_coe (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x z : V) (hxx : B x x = 0) (hzz : B z z = 0) (hxz : B x z = 2)
    (i : Fin 2) : (planeBasis B hB x z hxx hzz hxz i : V) = ![x,z] i :=
  Basis.span_apply _ _

theorem plane_nondegenerate (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x z : V) (hxx : B x x = 0) (hzz : B z z = 0) (hxz : B x z = 2) :
    (B.restrict (plane x z)).Nondegenerate := by
  intro v hv
  obtain ⟨a, b, hab⟩ := (mem_plane x z).mp v.property
  have hzx : B z x = 2 := by rw [hB.eq, hxz]
  have h1 := hv ⟨x, x_mem_plane x z⟩
  have h2 := hv ⟨z, z_mem_plane x z⟩
  change B v.val x = 0 at h1
  change B v.val z = 0 at h2
  rw [← hab] at h1 h2
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hxx, hzz, hxz, hzx, smul_eq_mul, mul_zero, zero_add, add_zero] at h1 h2
  have ha : a = 0 := by linear_combination (1/2 : K) * h2
  have hb : b = 0 := by linear_combination (1/2 : K) * h1
  apply Subtype.ext
  simp [← hab, ha, hb]

theorem plane_isCompl_orthogonal [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x z : V) (hxx : B x x = 0) (hzz : B z z = 0) (hxz : B x z = 2) :
    IsCompl (plane x z) (B.orthogonal (plane x z)) :=
  B.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl
    (plane_nondegenerate B hB x z hxx hzz hxz)

theorem restrict_nondegenerate_of_isCompl_kernel
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (C : Submodule K V) (hC : IsCompl (LinearMap.ker B) C) :
    (B.restrict C).Nondegenerate := by
  intro x hx
  have hker : (x : V) ∈ LinearMap.ker B := by
    apply LinearMap.ext
    intro y
    obtain ⟨a, c, hac, _⟩ := Submodule.existsUnique_add_of_isCompl hC y
    change B x y = 0
    rw [← hac, map_add]
    have ha : B x a = 0 := by
      rw [hB.eq]
      exact congrArg (fun f : V →ₗ[K] K => f x) a.property
    have hc : B x c = 0 := hx c
    rw [ha, hc, add_zero]
  apply Subtype.ext
  exact Submodule.disjoint_def.mp hC.disjoint x hker x.property

theorem kernel_restrict_orthogonal
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (P : Submodule K V) (hP : IsCompl P (B.orthogonal P)) :
    LinearMap.ker (B.restrict (B.orthogonal P)) =
      (LinearMap.ker B).comap (B.orthogonal P).subtype := by
  ext x
  constructor
  · intro hx
    apply LinearMap.ext
    intro y
    obtain ⟨p, w, hpw, _⟩ := Submodule.existsUnique_add_of_isCompl hP y
    change B x.val y = 0
    rw [← hpw, map_add]
    have hp : B x.val p = 0 := by
      rw [hB.eq]
      exact x.property p p.property
    have hw : B x.val w = 0 :=
      congrArg (fun f : (B.orthogonal P) →ₗ[K] K => f w) hx
    rw [hp, hw, add_zero]
  · intro hx
    apply LinearMap.ext
    intro y
    exact congrArg (fun f : V →ₗ[K] K => f y) hx

theorem kernel_le_orthogonal (B : LinearMap.BilinForm K V)
    (hB : B.IsSymm) (P : Submodule K V) :
    LinearMap.ker B ≤ B.orthogonal P := by
  intro x hx y _
  change B y x = 0
  rw [hB.eq]
  exact congrArg (fun f : V →ₗ[K] K => f y) hx

theorem finrank_kernel_restrict_orthogonal [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (P : Submodule K V) (hP : IsCompl P (B.orthogonal P)) :
    finrank K (LinearMap.ker (B.restrict (B.orthogonal P))) =
      finrank K (LinearMap.ker B) := by
  rw [kernel_restrict_orthogonal B hB P hP]
  exact (Submodule.comapSubtypeEquivOfLe (kernel_le_orthogonal B hB P)).finrank_eq

abbrev Index (m q : ℕ) := Fin m ⊕ (Fin q ⊕ Fin 2)

/-- A basis whose first block is the radical, whose middle block is
nondegenerate, and whose last two vectors form the prescribed hyperbolic pair. -/
structure Splitting [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (x : V) (m q : ℕ) where
  basis : Basis (Index m q) K V
  radical_dimension : m = finrank K (LinearMap.ker B)
  ambient_dimension : m + q + 2 = finrank K V
  radial_eq : basis (Sum.inr (Sum.inr 0)) = x
  radial_self : B x x = 0
  partner_self : B (basis (Sum.inr (Sum.inr 1))) (basis (Sum.inr (Sum.inr 1))) = 0
  radial_partner : B x (basis (Sum.inr (Sum.inr 1))) = 2
  radical_vectors : ∀ i, basis (Sum.inl i) ∈ LinearMap.ker B
  middle_orthogonal : ∀ j k, B (basis (Sum.inr (Sum.inr k)))
      (basis (Sum.inr (Sum.inl j))) = 0
  middle_nonsingular : Matrix.det (fun i j => B (basis (Sum.inr (Sum.inl i)))
      (basis (Sum.inr (Sum.inl j))) : Matrix (Fin q) (Fin q) K) ≠ 0

theorem exists_splitting [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x : V) (hxx : B x x = 0) (hxr : x ∉ LinearMap.ker B) :
    ∃ m q, Nonempty (Splitting B x m q) := by
  classical
  obtain ⟨z, hxz, hzz⟩ := exists_partner B hB x hxx hxr
  let P := plane (K := K) x z
  let W := B.orthogonal P
  let BW := B.restrict W
  have hBW : BW.IsSymm := by
    constructor
    intro a b
    exact hB.eq a b
  have hPW : IsCompl P W := plane_isCompl_orthogonal B hB x z hxx hzz hxz
  let A := LinearMap.ker BW
  obtain ⟨C, hC⟩ := A.exists_isCompl
  let ba := Module.finBasis K A
  let bc := Module.finBasis K C
  let bw := (ba.prod bc).map (A.prodEquivOfIsCompl C hC)
  let bp := planeBasis B hB x z hxx hzz hxz
  let be := (bw.prod bp).map (W.prodEquivOfIsCompl P hPW.symm)
  let b := be.reindex (Equiv.sumAssoc _ _ _)
  have hbA (i) : b (Sum.inl i) = ((ba i : W) : V) := by
    simp [b, be, bw, Basis.prod_apply]
    change ((ba i : W) : V) + 0 = _
    exact add_zero _
  have hbC (i) : b (Sum.inr (Sum.inl i)) = ((bc i : W) : V) := by
    simp [b, be, bw, Basis.prod_apply]
    change ((bc i : W) : V) + 0 = _
    exact add_zero _
  have hbP (i) : b (Sum.inr (Sum.inr i)) = ![x,z] i := by
    simp [b, be, bp, Basis.prod_apply]
    change (0 : V) + (planeBasis B hB x z hxx hzz hxz i : V) = _
    simp
  have hdimA : finrank K A = finrank K (LinearMap.ker B) :=
    finrank_kernel_restrict_orthogonal B hB P hPW
  have hdim : finrank K A + finrank K C + 2 = finrank K V := by
    simpa using (finrank_eq_card_basis b).symm
  refine ⟨finrank K A, finrank K C, ⟨{
    basis := b
    radical_dimension := hdimA
    ambient_dimension := hdim
    radial_eq := ?_
    radial_self := hxx
    partner_self := ?_
    radial_partner := ?_
    radical_vectors := ?_
    middle_orthogonal := ?_
    middle_nonsingular := ?_
  }⟩⟩
  · simpa using hbP 0
  · simpa [hbP] using hzz
  · simpa [hbP] using hxz
  · intro i
    rw [hbA]
    have hi := (ba i).property
    change (ba i : W) ∈ LinearMap.ker (B.restrict (B.orthogonal P)) at hi
    rw [kernel_restrict_orthogonal B hB P hPW] at hi
    exact hi
  · intro j k
    rw [hbP, hbC]
    exact (bc j).val.property _ (by
      apply Submodule.subset_span
      exact ⟨k, rfl⟩)
  · have hnd := restrict_nondegenerate_of_isCompl_kernel BW hBW C hC
    have hd := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bc).mp hnd
    have hm : (fun i j => B (b (Sum.inr (Sum.inl i))) (b (Sum.inr (Sum.inl j)))) =
        BilinForm.toMatrix bc (BW.restrict C) := by
      ext i j
      simp [BilinForm.toMatrix_apply, hbC, BW]
    rw [hm]
    exact hd

end HessianTheorem11.HyperbolicBasis
