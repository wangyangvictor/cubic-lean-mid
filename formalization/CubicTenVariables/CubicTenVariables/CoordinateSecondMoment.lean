import CubicTenVariables.ProjectiveFourierIdentity
import CubicTenVariables.BinarySliceCounting
import Mathlib.Analysis.RCLike.Basic

/-! Exact finite-field Parseval on a coordinate subspace of codimension
two. All frequencies, including zero, are included. The polynomial is
arbitrary: no irreducibility, point-count bound, or literature input is
used in these finite identities. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CoordinateSecondMoment
open MvPolynomial Matrix FiniteFieldFourier ProjectiveFourierIdentity BinarySliceCounting
open scoped BigOperators Classical

variable {k : Type*} [Field k] [Fintype k]

/-- The positive-sign, unnormalized Fourier transform on a finite vector space. -/
def transform {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : AddChar k ℂ)
    (f : (ι → k) → ℂ) (v : ι → k) : ℂ := ∑ x, f x * ψ (dotProduct v x)

/-- Orthogonality for any finite coordinate index type, including an empty one. -/
theorem sum_linear_phase {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (b : ι → k) :
    (∑ x : ι → k, ψ (dotProduct b x)) =
      if b = 0 then (Fintype.card k : ℂ)^(Fintype.card ι) else 0 := by
  classical
  by_cases hb : b = 0
  · simp [hb]
  · rw [if_neg hb]
    let χ : AddChar (ι → k) ℂ :=
      { toFun := fun x => ψ (dotProduct b x)
        map_zero_eq_one' := by simp
        map_add_eq_mul' := fun x y => by rw [dotProduct_add,ψ.map_add_eq_mul] }
    have hχ : χ ≠ 1 := by
      obtain ⟨j,hj⟩ : ∃ j, b j ≠ 0 := by
        by_contra! hh
        exact hb (funext hh)
      obtain ⟨c,hc⟩ := AddChar.ne_one_iff.mp hψ
      apply AddChar.ne_one_iff.mpr
      refine ⟨Pi.single j (c/b j),?_⟩
      change ψ (dotProduct b (Pi.single j (c/b j))) ≠ 1
      have he : dotProduct b (Pi.single j (c/b j)) = c := by
        rw [dotProduct_single]
        field_simp
      rwa [he]
    exact AddChar.sum_eq_zero_of_ne_one hχ

/-- The exact complex inner-product form of finite-field Parseval. -/
theorem transform_mul_conj_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (f : (ι → k) → ℂ) :
    (∑ v, transform ψ f v * starRingEnd ℂ (transform ψ f v)) =
      (Fintype.card k : ℂ)^(Fintype.card ι) *
        ∑ x, f x * starRingEnd ℂ (f x) := by
  classical
  have hchar (v x y : ι → k) :
      ψ (dotProduct v x) * starRingEnd ℂ (ψ (dotProduct v y)) =
        ψ (dotProduct v (x-y)) := by
    rw [dotProduct_sub,sub_eq_add_neg,AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_conj]
  calc
    _ = ∑ v : ι → k, ∑ x : ι → k, ∑ y : ι → k,
        (f x * ψ (dotProduct v x)) *
          (starRingEnd ℂ (f y) * starRingEnd ℂ (ψ (dotProduct v y))) := by
      simp only [transform,map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      exact Finset.sum_comm
    _ = ∑ x : ι → k, ∑ y : ι → k, ∑ v : ι → k,
        (f x * ψ (dotProduct v x)) *
          (starRingEnd ℂ (f y) * starRingEnd ℂ (ψ (dotProduct v y))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ x : ι → k, ∑ y : ι → k,
        (f x * starRingEnd ℂ (f y)) *
          (if x = y then (Fintype.card k : ℂ)^(Fintype.card ι) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      calc
        _ = (f x * starRingEnd ℂ (f y)) *
            ∑ v : ι → k, ψ (dotProduct v (x-y)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v hv
          rw [←hchar]
          ring
        _ = _ := by
          have he := sum_linear_phase ψ hψ (x-y)
          simpa only [dotProduct_comm,sub_eq_zero] using
            congrArg (fun z : ℂ => (f x * starRingEnd ℂ (f y))*z) he
    _ = _ := by simp [mul_ite,Finset.mul_sum,mul_comm]

/-- Finite-field Parseval with real squared norms and its exact cardinality. -/
theorem transform_norm_sq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (f : (ι → k) → ℂ) :
    (∑ v, ‖transform ψ f v‖^2) =
      (Fintype.card k : ℝ)^(Fintype.card ι) * ∑ x, ‖f x‖^2 := by
  apply Complex.ofReal_injective
  simpa only [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_sum,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast] using
      transform_mul_conj_sum ψ hψ f

variable {n : ℕ}

/-- Number of actual affine zeros on the selected two-coordinate slice. -/
def sliceCount (F : MvPolynomial (Fin n) k) (e : Fin 2 ↪ Fin n)
    (w : Complement e → k) : ℕ :=
  (Finset.univ.filter fun z : Fin 2 → k => eval (combine e z w) F = 0).card

omit [Fintype k] in
/-- The chosen coordinate-plane frequency has exactly the complementary
linear phase on every binary slice. -/
theorem dotProduct_combine_zero (e : Fin 2 ↪ Fin n) (v w : Complement e → k)
    (z : Fin 2 → k) :
    dotProduct (combine e 0 v) (combine e z w) = dotProduct v w := by
  unfold dotProduct
  rw [sum_split e]
  simp only [combine_selected,combine_complement_index,Pi.zero_apply,zero_mul,
    Finset.sum_const_zero,zero_add]

omit [Fintype k] in
theorem combine_zero_eq_zero_iff (e : Fin 2 ↪ Fin n) (v : Complement e → k) :
    combine e 0 v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    funext i
    have he := congrFun hv i.val
    simpa only [combine_complement_index,Pi.zero_apply] using he
  · rintro rfl
    funext i
    simp only [combine]
    cases (indexEquiv e).symm i <;> rfl

/-- Grouping the literal affine zero sum by the complementary coordinates. -/
theorem zeroFiberSum_eq_slices (ψ : AddChar k ℂ) (F : MvPolynomial (Fin n) k)
    (e : Fin 2 ↪ Fin n) (v : Complement e → k) :
    zeroFiberSum ψ F (combine e 0 v) =
      ∑ w : Complement e → k, (sliceCount F e w : ℂ)*ψ (dotProduct v w) := by
  classical
  unfold zeroFiberSum
  rw [Finset.sum_filter,←Equiv.sum_comp ((splitEquiv e k).symm)]
  simp only [Fintype.sum_prod_type,splitEquiv_symm,dotProduct_combine_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,sliceCount]

/-- The main term at frequency zero is precisely the Fourier transform
of the constant q on the (n−2)-dimensional complementary vector space. -/
theorem constant_transform (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (e : Fin 2 ↪ Fin n) (v : Complement e → k) :
    (∑ w : Complement e → k, (Fintype.card k : ℂ)*ψ (dotProduct v w)) =
      if combine e 0 v = 0 then (Fintype.card k : ℂ)^(n-1) else 0 := by
  have hn : 2 ≤ n := by
    have h := Fintype.card_le_of_injective e e.injective
    simpa only [Fintype.card_fin] using h
  rw [←Finset.mul_sum,sum_linear_phase ψ hψ v,card_complement]
  simp only [combine_zero_eq_zero_iff]
  by_cases hv : v = 0
  · simp only [hv,if_true]
    have he : n-1 = (n-2)+1 := by omega
    rw [he,pow_succ']
  · simp only [hv,if_false,mul_zero]

/-- The manuscript's T at every frequency in the coordinate plane is
the Fourier transform of the literal slice count minus q. -/
theorem normalized_eq_transform (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) k) (e : Fin 2 ↪ Fin n) (v : Complement e → k) :
    normalizedFourierSum ψ F (combine e 0 v) =
      transform ψ (fun w => (sliceCount F e w : ℂ) - (Fintype.card k : ℂ)) v := by
  unfold normalizedFourierSum transform
  rw [zeroFiberSum_eq_slices,←constant_transform ψ hψ e v,←Finset.sum_sub_distrib]
  simp only [sub_mul]

/-- Exact coordinate-plane second moment, including zero frequency.
No estimate on an individual slice is assumed here. -/
theorem coordinate_second_moment (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) k) (e : Fin 2 ↪ Fin n) :
    (∑ v : Complement e → k, ‖normalizedFourierSum ψ F (combine e 0 v)‖^2) =
      (Fintype.card k : ℝ)^(n-2) *
        ∑ w : Complement e → k, ((sliceCount F e w : ℝ) - (Fintype.card k : ℝ))^2 := by
  simp_rw [normalized_eq_transform ψ hψ F e]
  rw [transform_norm_sq_sum ψ hψ
    (fun w : Complement e → k => (sliceCount F e w : ℂ) - (Fintype.card k : ℂ)),
    card_complement]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  have he : ((sliceCount F e w : ℂ) - (Fintype.card k : ℂ)) =
      Complex.ofReal ((sliceCount F e w : ℝ) - (Fintype.card k : ℝ)) := by push_cast; rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- The complementary-coordinate parametrization is a genuine bijection
onto the plane where the two selected frequency coordinates vanish. -/
def planeEquiv (e : Fin 2 ↪ Fin n) :
    (Complement e → k) ≃ {v : Fin n → k // ∀ j : Fin 2, v (e j) = 0} where
  toFun v := ⟨combine e 0 v,fun j => combine_selected e 0 v j⟩
  invFun v := fun i => v.val i.val
  left_inv v := by
    funext i
    exact combine_complement_index e 0 v i
  right_inv v := by
    apply Subtype.ext
    funext i
    change combine e 0 (fun j : Complement e => v.val j.val) i = v.val i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j,rfl⟩ := hi
      rw [combine_selected]
      exact (v.property j).symm
    · exact combine_complement e 0 (fun j => v.val j.val) i hi

/-- The exact identity with the left side summed literally over all
ambient vectors satisfying the two coordinate-plane equations. -/
theorem coordinate_plane_second_moment (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) k) (e : Fin 2 ↪ Fin n) :
    (∑ v ∈ Finset.univ.filter (fun v : Fin n → k => ∀ j : Fin 2, v (e j) = 0),
      ‖normalizedFourierSum ψ F v‖^2) =
      (Fintype.card k : ℝ)^(n-2) *
        ∑ w : Complement e → k, ((sliceCount F e w : ℝ) - (Fintype.card k : ℝ))^2 := by
  classical
  calc
    _ = ∑ v : {v : Fin n → k // ∀ j : Fin 2, v (e j) = 0},
        ‖normalizedFourierSum ψ F v.val‖^2 :=
      Finset.sum_subtype _ (by simp) _
    _ = ∑ v : Complement e → k, ‖normalizedFourierSum ψ F (combine e 0 v)‖^2 :=
      (Equiv.sum_comp (planeEquiv e) (fun v => ‖normalizedFourierSum ψ F v.val‖^2)).symm
    _ = _ := coordinate_second_moment ψ hψ F e

end CubicTenVariables.CoordinateSecondMoment
