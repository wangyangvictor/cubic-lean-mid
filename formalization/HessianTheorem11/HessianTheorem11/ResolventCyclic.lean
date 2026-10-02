import HessianTheorem11.IsotropicDual

/-! Actual cyclic subspaces of self-adjoint endomorphisms with vanishing
moments, and the common invariant isotropic space in the fixed-vector case. -/
noncomputable section
namespace HessianTheorem11.ResolventCyclic
open Module Submodule
variable {K A V : Type*} [Field K] [CharZero K]
  [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def TotallyIsotropic (B : LinearMap.BilinForm K V) (W : Submodule K V) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, B u v = 0

def Preserves (T : Module.End K V) (W : Submodule K V) : Prop :=
  ∀ v ∈ W, T v ∈ W

def cyclicSpan (T : Module.End K V) (v : V) : Submodule K V :=
  span K (Set.range fun j : ℕ => (T^j) v)

theorem cyclicSpan_mem (T : Module.End K V) (v : V) (j : ℕ) :
    (T^j) v ∈ cyclicSpan T v := subset_span ⟨j,rfl⟩

theorem cyclicSpan_self (T : Module.End K V) (v : V) : v ∈ cyclicSpan T v := by
  simpa using cyclicSpan_mem T v 0

theorem cyclicSpan_preserves (T : Module.End K V) (v : V) :
    Preserves T (cyclicSpan T v) := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨j,rfl⟩ := hu
    simpa [pow_succ',Module.End.mul_apply] using cyclicSpan_mem T v (j+1)
  | zero => simp
  | add u w hu hw ihu ihw => simpa using Submodule.add_mem _ ihu ihw
  | smul c u hu ih => simpa using Submodule.smul_mem _ c ih

theorem power_pairing (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (hT : ∀ u v, B (T u) v = B u (T v)) (u v : V) (i j : ℕ) :
    B ((T^i) u) ((T^j) v) = B u ((T^(i+j)) v) := by
  induction i generalizing j with
  | zero => simp
  | succ i ih =>
    rw [pow_succ',Module.End.mul_apply,hT]
    rw [← Module.End.mul_apply,← pow_succ',ih]
    congr 3
    omega

theorem cyclicSpan_isotropic (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (hT : ∀ u v, B (T u) v = B u (T v)) (v : V)
    (hm : ∀ j : ℕ, B v ((T^j) v) = 0) : TotallyIsotropic B (cyclicSpan T v) := by
  intro u hu w hw
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i,rfl⟩ := hu
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨j,rfl⟩ := hw; rw [power_pairing B T hT]; exact hm _
    | zero => simp
    | add a b ha hb iha ihb => simp [iha,ihb]
    | smul c a ha ih => simp [ih]
  | zero => simp
  | add a b ha hb iha ihb => simp [iha,ihb]
  | smul c a ha ih => simp [ih]

theorem isotropic_finrank_le_two (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hn : B.Nondegenerate) (hd : finrank K V = 4)
    (W : Submodule K V) (hW : TotallyIsotropic B W) : finrank K W ≤ 2 := by
  have h := IsotropicDual.isotropic_finrank_bound B hB hn W hW
  omega

theorem range_isotropic (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (e : A →ₗ[K] V) (h : ∀ a, B (e a) (e a) = 0) :
    TotallyIsotropic B (LinearMap.range e) := by
  rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
  have he := h (a+b)
  simp only [map_add,LinearMap.add_apply] at he
  rw [h a,h b,hB.eq (e b) (e a)] at he
  linear_combination he / 2

def firstSpan (M : A →ₗ[K] Module.End K V) (v : V) : Submodule K V :=
  (K ∙ v) ⊔ span K (Set.range fun a => M a v)

theorem firstSpan_isotropic (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (M : A →ₗ[K] Module.End K V)
    (hM : ∀ a u v, B (M a u) v = B u (M a v)) (v : V)
    (hm : ∀ a (j : ℕ), B v (((M a)^j) v) = 0) : TotallyIsotropic B (firstSpan M v) := by
  have hvv : B v v = 0 := by simpa using hm 0 0
  have hvM (a) : B v (M a v) = 0 := by simpa using hm a 1
  have hMM (a b) : B (M a v) (M b v) = 0 := by
    have haa : B (M a v) (M a v) = 0 := by
      rw [hM]; simpa [pow_two,Module.End.mul_apply] using hm a 2
    have hbb : B (M b v) (M b v) = 0 := by
      rw [hM]; simpa [pow_two,Module.End.mul_apply] using hm b 2
    have hab : B (M (a+b) v) (M (a+b) v) = 0 := by
      rw [hM]; simpa [pow_two,Module.End.mul_apply] using hm (a+b) 2
    simp only [map_add,LinearMap.add_apply] at hab
    rw [haa,hbb,hB.eq (M b v) (M a v)] at hab
    linear_combination hab / 2
  have hspan : firstSpan M v = span K ({v} ∪ Set.range (fun a => M a v)) := by
    rw [span_union]; rfl
  rw [hspan]
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hx with hx | ⟨a,rfl⟩ <;> rcases hy with hy | ⟨b,rfl⟩
      · have hx' : x = v := hx; have hy' : y = v := hy
        subst x; subst y; exact hvv
      · have hx' : x = v := hx
        subst x; exact hvM b
      · have hy' : y = v := hy
        subst y; rw [hB.eq]; exact hvM a
      · exact hMM a b
    | zero => simp
    | add a b ha hb iha ihb => simp [iha,ihb]
    | smul c a ha ih => simp [ih]
  | zero => simp
  | add a b ha hb iha ihb => simp [iha,ihb]
  | smul c a ha ih => simp [ih]

theorem isotropic_eq_of_common_pair
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hn : B.Nondegenerate) (hd : finrank K V = 4)
    (W C : Submodule K V) (hW : TotallyIsotropic B W) (hC : TotallyIsotropic B C)
    (v w : V) (hv : v ≠ 0) (hw : w ∉ K ∙ v)
    (hvW : v ∈ W) (hwW : w ∈ W) (hvC : v ∈ C) (hwC : w ∈ C) : W = C := by
  let P := (K ∙ v) ⊔ (K ∙ w)
  have hPdim : 2 ≤ finrank K P := by
    by_contra hh
    have he : K ∙ v = P := Submodule.eq_of_le_of_finrank_le le_sup_left
      (by rw [finrank_span_singleton hv]; omega)
    apply hw
    rw [he]
    exact (show (K ∙ w) ≤ P from le_sup_right) (mem_span_singleton_self w)
  have hPW : P ≤ W := sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvW))
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hwW))
  have hPC : P ≤ C := sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvC))
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hwC))
  have heW : P = W := Submodule.eq_of_le_of_finrank_le hPW
    ((isotropic_finrank_le_two B hB hn hd W hW).trans hPdim)
  have heC : P = C := Submodule.eq_of_le_of_finrank_le hPC
    ((isotropic_finrank_le_two B hB hn hd C hC).trans hPdim)
  exact heW.symm.trans heC

theorem firstSpan_self (M : A →ₗ[K] Module.End K V) (v : V) :
    v ∈ firstSpan M v := (show (K ∙ v) ≤ firstSpan M v from le_sup_left) (mem_span_singleton_self v)

theorem firstSpan_image (M : A →ₗ[K] Module.End K V) (v : V) (a : A) :
    M a v ∈ firstSpan M v := (show span K (Set.range fun a => M a v) ≤ firstSpan M v from le_sup_right) (subset_span ⟨a,rfl⟩)

/-- A fixed vector with vanishing moments for a linear self-adjoint family
has a single common invariant isotropic hull in dimension four. -/
theorem firstSpan_preserves (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hn : B.Nondegenerate) (hd : finrank K V = 4)
    (M : A →ₗ[K] Module.End K V)
    (hM : ∀ a u v, B (M a u) v = B u (M a v)) (v : V)
    (hm : ∀ a (j : ℕ), B v (((M a)^j) v) = 0) :
    ∀ a, Preserves (M a) (firstSpan M v) := by
  classical
  by_cases hv : v = 0
  · subst v
    intro a u hu
    have hz : firstSpan M 0 = ⊥ := by simp [firstSpan]
    rw [hz] at hu ⊢
    have hu0 : u = 0 := hu
    simp [hu0]
  have hiso := firstSpan_isotropic B hB M hM v hm
  have hgeneric (a : A) (ha : M a v ∉ K ∙ v) : Preserves (M a) (firstSpan M v) := by
    have he := isotropic_eq_of_common_pair B hB hn hd
      (firstSpan M v) (cyclicSpan (M a) v) hiso
      (cyclicSpan_isotropic B (M a) (hM a) v (hm a)) v (M a v) hv ha
      (firstSpan_self M v) (firstSpan_image M v a)
      (cyclicSpan_self (M a) v) (by simpa using cyclicSpan_mem (M a) v 1)
    rw [he]
    exact cyclicSpan_preserves _ _
  by_cases hall : ∀ a, M a v ∈ K ∙ v
  · have he : firstSpan M v = K ∙ v := by
      apply le_antisymm
      · exact sup_le le_rfl (span_le.mpr (by rintro _ ⟨a,rfl⟩; exact hall a))
      · exact le_sup_left
    intro a u hu
    rw [he] at hu ⊢
    obtain ⟨c,rfl⟩ := mem_span_singleton.mp hu
    simpa using (K ∙ v).smul_mem c (hall a)
  · push_neg at hall
    obtain ⟨b,hb⟩ := hall
    intro a
    by_cases ha : M a v ∈ K ∙ v
    · have hab : M (a+b) v ∉ K ∙ v := by
        intro hh
        apply hb
        have hdif := (K ∙ v).sub_mem hh ha
        simpa using hdif
      intro u hu
      have hsum := hgeneric (a+b) hab u hu
      have hbu := hgeneric b hb u hu
      have hdiff := (firstSpan M v).sub_mem hsum hbu
      simpa using hdiff
    · exact hgeneric a ha

end HessianTheorem11.ResolventCyclic
