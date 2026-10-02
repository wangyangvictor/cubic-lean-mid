import HessianTheorem11.IsotropicDual
import HessianTheorem11.CubicHyperbolicBasis
import HessianTheorem11.SaturatedCoisotropy

/-! Coisotropic symmetric-form splitting with a prescribed isotropic
radial vector. This file contains only actual finite-dimensional linear
algebra, with no geometric or normal-form input. -/
noncomputable section
namespace HessianTheorem11.CoisotropicBasis
open Module Submodule
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_complement_containing_vector (R : Submodule K V) (x : V) (hx : x ∉ R) :
    ∃ C : Submodule K V, IsCompl R C ∧ x ∈ C := by
  classical
  obtain ⟨I, b, i, hix, _, hbR⟩ := exists_set_basis_simultaneous (⊤ : Submodule K V) R x
    (Submodule.mem_top) hx
  let J : Set I := {j | b j ∈ R}
  let C := span K (b '' Jᶜ)
  have hc : IsCompl R C := by
    rw [← hbR]
    exact b.linearIndependent.isCompl_span_image b.span_eq
      (show IsCompl J Jᶜ from isCompl_compl)
  refine ⟨C,hc,?_⟩
  rw [← hix]
  apply Submodule.subset_span
  refine ⟨i, ?_, rfl⟩
  change b i ∉ R
  rwa [hix]

theorem exists_fin_basis_containing (x : V) (hx : x ≠ 0) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)), b i = x := by
  classical
  obtain ⟨I, b, i, hi, _, _⟩ := exists_set_basis_simultaneous
    (⊤ : Submodule K V) ⊥ x (Submodule.mem_top) (by simpa using hx)
  letI : Finite I := Module.Finite.finite_basis b
  letI : Fintype I := Fintype.ofFinite I
  let e : I ≃ Fin (finrank K V) := (Fintype.equivFin I).trans
    (finCongr (finrank_eq_card_basis b).symm)
  exact ⟨b.reindex e, e i, by simpa using hi⟩

abbrev NondegenerateIndex (d q : ℕ) := Fin q ⊕ (Fin d ⊕ Fin d)

structure NondegenerateData (B : LinearMap.BilinForm K V) (T : Submodule K V)
    (x : V) (d q : ℕ) where
  basis : Basis (NondegenerateIndex d q) K V
  radial : Fin d
  radial_eq : basis (Sum.inr (Sum.inl radial)) = x
  codimension : d + finrank K T = finrank K V
  dimension : 2*d+q = finrank K V
  tangent_middle : ∀ i, basis (Sum.inl i) ∈ T
  tangent_isotropic : ∀ i, basis (Sum.inr (Sum.inl i)) ∈ T
  isotropic_left : ∀ i j, B (basis (Sum.inr (Sum.inl i)))
    (basis (Sum.inr (Sum.inl j))) = 0
  isotropic_right : ∀ i j, B (basis (Sum.inr (Sum.inr i)))
    (basis (Sum.inr (Sum.inr j))) = 0
  pairing : ∀ i j, B (basis (Sum.inr (Sum.inl i)))
    (basis (Sum.inr (Sum.inr j))) = if i=j then 1 else 0
  middle_orthogonal_left : ∀ i j, B (basis (Sum.inl i)) (basis (Sum.inr (Sum.inl j))) = 0
  middle_orthogonal_right : ∀ i j, B (basis (Sum.inl i)) (basis (Sum.inr (Sum.inr j))) = 0
  middle_nonsingular : Matrix.det ((fun i j => B (basis (Sum.inl i))
    (basis (Sum.inl j))) : Matrix (Fin q) (Fin q) K) ≠ 0

theorem exists_nondegenerate_data
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hn : B.Nondegenerate)
    (T : Submodule K V) (hco : B.orthogonal T ≤ T)
    (x : V) (hx : x ∈ B.orthogonal T) (hx0 : x ≠ 0) :
    ∃ d q, Nonempty (NondegenerateData B T x d q) := by
  classical
  let W := B.orthogonal T
  have hW : ∀ u ∈ W, ∀ v ∈ W, B u v = 0 := by
    intro u hu v hv
    rw [hB.eq]
    exact hu v (hco hv)
  obtain ⟨bw, radial, hradial⟩ := exists_fin_basis_containing (K := K)
    (⟨x,hx⟩ : W) (by intro he; exact hx0 (congrArg Subtype.val he))
  obtain ⟨z, hwz, hzz⟩ := IsotropicDual.exists_dual_family B hB hn W hW bw
  let w := fun i => (bw i : V)
  have hww : ∀ i j, B (w i) (w j) = 0 := fun i j => hW _ (bw i).property _ (bw j).property
  have hli := IsotropicDual.hyperbolic_family_independent B hB w z hww hzz hwz
  let P := span K (Set.range (Sum.elim w z))
  let H := B.orthogonal P
  have hPn : (B.restrict P).Nondegenerate :=
    IsotropicDual.hyperbolic_span_nondegenerate B hB w z hww hzz hwz
  have hPH : IsCompl P H := B.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hPn
  have hHn : (B.restrict H).Nondegenerate := by
    apply B.nondegenerate_restrict_of_disjoint_orthogonal hB.isRefl
    change Disjoint H (B.orthogonal (B.orthogonal P))
    rw [LinearMap.BilinForm.orthogonal_orthogonal hn hB.isRefl]
    exact hPH.disjoint.symm
  let bp := Basis.span hli
  let bh := Module.finBasis K H
  let b := (bh.prod bp).map (H.prodEquivOfIsCompl P hPH.symm)
  have hbH (i) : b (Sum.inl i) = (bh i : V) := by
    simp [b, Basis.prod_apply]
    change (bh i : V) + 0 = _
    exact add_zero _
  have hbK (i) : b (Sum.inr (Sum.inl i)) = w i := by
    simp [b, Basis.prod_apply]
    change (0 : V) + (bp (Sum.inl i) : V) = w i
    simp [bp, Basis.span_apply]
  have hbD (i) : b (Sum.inr (Sum.inr i)) = z i := by
    simp [b, Basis.prod_apply]
    change (0 : V) + (bp (Sum.inr i) : V) = z i
    simp [bp, Basis.span_apply]
  have hWP : W ≤ P := by
    intro u hu
    have hu' := bw.sum_repr ⟨u,hu⟩
    have he : (∑ i, bw.repr ⟨u,hu⟩ i • w i) = u := by
      have hh := congrArg W.subtype hu'
      simpa only [map_sum, map_smul] using hh
    rw [← he]
    apply P.sum_mem
    intro i _
    exact P.smul_mem _ (Submodule.subset_span ⟨Sum.inl i,rfl⟩)
  have hHT : H ≤ T := by
    intro u hu
    have hh : u ∈ B.orthogonal W := fun v hv => hu v (hWP hv)
    have he := LinearMap.BilinForm.orthogonal_orthogonal hn hB.isRefl T
    change u ∈ B.orthogonal (B.orthogonal T) at hh
    rwa [he] at hh
  refine ⟨finrank K W, finrank K H, ⟨{
    basis := b
    radial := radial
    radial_eq := ?_
    codimension := ?_
    dimension := ?_
    tangent_middle := ?_
    tangent_isotropic := ?_
    isotropic_left := ?_
    isotropic_right := ?_
    pairing := ?_
    middle_orthogonal_left := ?_
    middle_orthogonal_right := ?_
    middle_nonsingular := ?_ }⟩⟩
  · rw [hbK]
    exact congrArg Subtype.val hradial
  · have hd := LinearMap.BilinForm.finrank_orthogonal hn hB.isRefl T
    have hle := Submodule.finrank_le T
    change finrank K W = _ at hd
    omega
  · have hd := finrank_eq_card_basis b
    simpa [NondegenerateIndex, two_mul, add_comm, add_left_comm, add_assoc] using hd.symm
  · intro i
    rw [hbH]
    exact hHT (bh i).property
  · intro i
    rw [hbK]
    exact hco (bw i).property
  · intro i j
    rw [hbK, hbK]
    exact hww i j
  · intro i j
    rw [hbD, hbD]
    exact hzz i j
  · intro i j
    rw [hbK, hbD]
    exact hwz i j
  · intro i j
    rw [hbH, hbK, hB.eq]
    exact (bh i).property (w j) (Submodule.subset_span ⟨Sum.inl j,rfl⟩)
  · intro i j
    rw [hbH, hbD, hB.eq]
    exact (bh i).property (z j) (Submodule.subset_span ⟨Sum.inr j,rfl⟩)
  · have hd := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bh).mp hHn
    have hm : (fun i j => B (b (Sum.inl i)) (b (Sum.inl j))) =
        BilinForm.toMatrix bh (B.restrict H) := by
      ext i j
      simp [BilinForm.toMatrix_apply, hbH]
    rw [hm]
    exact hd

theorem restrict_coisotropic_of_kernel_complement
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (T C : Submodule K V) (hC : IsCompl (LinearMap.ker B) C)
    (hRT : LinearMap.ker B ≤ T) (hco : B.orthogonal T ≤ T) :
    (B.restrict C).orthogonal (T.comap C.subtype) ≤ T.comap C.subtype := by
  intro u hu
  apply hco
  intro t ht
  obtain ⟨r,c,hrc,_⟩ := Submodule.existsUnique_add_of_isCompl hC t
  have hcT : (c : V) ∈ T := by
    have he : (c : V) = t-r := by rw [← hrc]; abel
    rw [he]
    exact T.sub_mem ht (hRT r.property)
  change B t u = 0
  rw [← hrc, map_add, LinearMap.add_apply]
  have hr : B r u = 0 := congrArg (fun f : V →ₗ[K] K => f u) r.property
  have hc : B c u = 0 := hu c hcT
  rw [hr,hc,add_zero]

theorem finrank_comap_add_kernel
    (B : LinearMap.BilinForm K V) (T C : Submodule K V)
    (hC : IsCompl (LinearMap.ker B) C) (hRT : LinearMap.ker B ≤ T) :
    finrank K (T.comap C.subtype) + finrank K (LinearMap.ker B) = finrank K T := by
  have hsup : T ⊔ C = ⊤ := by
    apply top_unique
    rw [← hC.codisjoint.eq_top]
    exact sup_le_sup_right hRT C
  have hd := Submodule.finrank_sup_add_finrank_inf_eq T C
  rw [hsup, finrank_top] at hd
  have he := (Submodule.equivMapOfInjective C.subtype C.subtype_injective
    (T.comap C.subtype)).finrank_eq
  rw [Submodule.map_comap_subtype, inf_comm] at he
  have hc := Submodule.finrank_add_eq_of_isCompl hC
  omega

abbrev Index (m d q : ℕ) := Fin m ⊕ NondegenerateIndex d q

/-- An actual ambient basis adapted simultaneously to the Hessian radical,
the coisotropic tangent subspace, and the prescribed radial vector. -/
structure Data (B : LinearMap.BilinForm K V) (T : Submodule K V)
    (x : V) (m d q : ℕ) where
  basis : Basis (Index m d q) K V
  radial : Fin d
  radial_eq : basis (Sum.inr (Sum.inr (Sum.inl radial))) = x
  radical_dimension : m = finrank K (LinearMap.ker B)
  codimension : d + finrank K T = finrank K V
  dimension : m + 2*d + q = finrank K V
  radical_vectors : ∀ i, basis (Sum.inl i) ∈ LinearMap.ker B
  tangent_middle : ∀ i, basis (Sum.inr (Sum.inl i)) ∈ T
  tangent_isotropic : ∀ i, basis (Sum.inr (Sum.inr (Sum.inl i))) ∈ T
  isotropic_left : ∀ i j, B (basis (Sum.inr (Sum.inr (Sum.inl i))))
    (basis (Sum.inr (Sum.inr (Sum.inl j)))) = 0
  isotropic_right : ∀ i j, B (basis (Sum.inr (Sum.inr (Sum.inr i))))
    (basis (Sum.inr (Sum.inr (Sum.inr j)))) = 0
  pairing : ∀ i j, B (basis (Sum.inr (Sum.inr (Sum.inl i))))
    (basis (Sum.inr (Sum.inr (Sum.inr j)))) = if i=j then 1 else 0
  middle_orthogonal_left : ∀ i j, B (basis (Sum.inr (Sum.inl i)))
    (basis (Sum.inr (Sum.inr (Sum.inl j)))) = 0
  middle_orthogonal_right : ∀ i j, B (basis (Sum.inr (Sum.inl i)))
    (basis (Sum.inr (Sum.inr (Sum.inr j)))) = 0
  middle_nonsingular : Matrix.det ((fun i j => B (basis (Sum.inr (Sum.inl i)))
    (basis (Sum.inr (Sum.inl j)))) : Matrix (Fin q) (Fin q) K) ≠ 0

theorem exists_data
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (T : Submodule K V) (hRT : LinearMap.ker B ≤ T) (hco : B.orthogonal T ≤ T)
    (x : V) (hx : x ∈ B.orthogonal T) (hxr : x ∉ LinearMap.ker B) :
    ∃ m d q, Nonempty (Data B T x m d q) := by
  classical
  let R := LinearMap.ker B
  obtain ⟨C,hC,hxC⟩ := exists_complement_containing_vector R x hxr
  let BC := B.restrict C
  let TC := T.comap C.subtype
  have hBC : BC.IsSymm := ⟨fun u v => hB.eq u v⟩
  have hBn : BC.Nondegenerate :=
    HyperbolicBasis.restrict_nondegenerate_of_isCompl_kernel B hB C hC
  have hcoC : BC.orthogonal TC ≤ TC :=
    restrict_coisotropic_of_kernel_complement B hB T C hC hRT hco
  have hxC' : (⟨x,hxC⟩ : C) ∈ BC.orthogonal TC := fun u hu => hx u hu
  have hx0 : (⟨x,hxC⟩ : C) ≠ 0 := by
    intro he
    apply hxr
    have hzero : x = 0 := congrArg Subtype.val he
    rw [hzero]
    exact Submodule.zero_mem _
  obtain ⟨d,q,⟨D⟩⟩ := exists_nondegenerate_data BC hBC hBn TC hcoC ⟨x,hxC⟩ hxC' hx0
  let br := Module.finBasis K R
  let b := (br.prod D.basis).map (R.prodEquivOfIsCompl C hC)
  have hbR (i) : b (Sum.inl i) = (br i : V) := by
    simp [b, Basis.prod_apply]
  have hbC (i) : b (Sum.inr i) = (D.basis i : V) := by
    simp [b, Basis.prod_apply]
  have hdim := Submodule.finrank_add_eq_of_isCompl hC
  have hdimT := finrank_comap_add_kernel B T C hC hRT
  refine ⟨finrank K R,d,q,⟨{
    basis := b
    radial := D.radial
    radial_eq := ?_
    radical_dimension := rfl
    codimension := ?_
    dimension := ?_
    radical_vectors := ?_
    tangent_middle := ?_
    tangent_isotropic := ?_
    isotropic_left := ?_
    isotropic_right := ?_
    pairing := ?_
    middle_orthogonal_left := ?_
    middle_orthogonal_right := ?_
    middle_nonsingular := ?_ }⟩⟩
  · rw [hbC]
    exact congrArg Subtype.val D.radial_eq
  · have h := D.codimension
    change finrank K TC + finrank K R = _ at hdimT
    omega
  · have h := D.dimension
    omega
  · intro i
    rw [hbR]
    exact (br i).property
  · intro i
    rw [hbC]
    exact D.tangent_middle i
  · intro i
    rw [hbC]
    exact D.tangent_isotropic i
  · intro i j
    rw [hbC,hbC]
    exact D.isotropic_left i j
  · intro i j
    rw [hbC,hbC]
    exact D.isotropic_right i j
  · intro i j
    rw [hbC,hbC]
    exact D.pairing i j
  · intro i j
    rw [hbC,hbC]
    exact D.middle_orthogonal_left i j
  · intro i j
    rw [hbC,hbC]
    exact D.middle_orthogonal_right i j
  · simpa only [hbC] using D.middle_nonsingular

end HessianTheorem11.CoisotropicBasis
