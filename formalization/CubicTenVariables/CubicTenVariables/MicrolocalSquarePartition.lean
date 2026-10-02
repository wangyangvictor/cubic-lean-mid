import CubicTenVariables.MicrolocalPromotedPartition
import CubicTenVariables.HomogeneousPromotionScaling
import CubicTenVariables.MicrolocalTerminalPrimeCertificate
import CubicTenVariables.AmbientProgressionCount

/-! The actual unpromoted rational depth partition, with seven levels
including the separate origin. Its progression counts, common constants,
and nonzero rational scaling are proved from the same incidence geometry.
No prime-square estimate or new literature premise is assumed here. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.MicrolocalSquarePartition
open MvPolynomial HessianTheorem11 RationalConeClosure
open ProjectiveMicrolocalData ProjectiveMicrolocalModels
open ConeComponentProgressionCount
open scoped BigOperators

variable {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}

/-- Empty promotion sets preserve the original rational depth layers. -/
def emptyPromotion : ℕ → Set (Fin 10 → ℚ) := fun _ => ∅

theorem empty_compatible (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) :
    MicrolocalPromotedPartition.Compatible f emptyPromotion :=
  ⟨rfl,rfl,fun _ _ => Set.empty_subset _⟩

/-- The six nonzero old layers and the origin, all on the same incidence. -/
def part (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (j : Fin 7) : Set (Fin 10 → ℚ) :=
  if hj : j.val < 6 then
    MicrolocalPromotedPartition.part f emptyPromotion ⟨j.val,hj⟩ else {0}

/-- The progression-count exponents are 10,8,7,6,5,1,0. -/
def exponent (j : Fin 7) : ℕ :=
  if j.val=0 then 10 else if j.val<5 then 9-j.val else if j.val=5 then 1 else 0

theorem exponent_eq_table (j : Fin 7) : exponent j = ![10,8,7,6,5,1,0] j := by
  fin_cases j <;> rfl

theorem part_of_lt_six (j : Fin 7) (hj : j.val < 6) :
    part f j = MicrolocalPromotedPartition.part f emptyPromotion ⟨j.val,hj⟩ := by
  simp only [part,dif_pos hj]

@[simp] theorem part_six : part f ⟨6,by decide⟩ = {0} := by simp [part]

/-- Literal old-layer formula at levels zero through four. -/
theorem part_eq_layer (j : Fin 7) (hj : j.val < 5) :
    part f j = (MicrolocalPromotedPartition.filtration f j.val \
      MicrolocalPromotedPartition.filtration f (j.val+1)) \ {0} := by
  rw [part_of_lt_six j (by omega),
    MicrolocalPromotedPartition.part_eq_source emptyPromotion ⟨j.val,by omega⟩ hj]
  simp only [emptyPromotion,Set.diff_empty,Set.union_empty]

@[simp] theorem part_five :
    part f ⟨5,by decide⟩ = rationalPoints (ProjectiveMicrolocalDepth.depth f 5) \ {0} := by
  rw [part_of_lt_six _ (by decide),MicrolocalPromotedPartition.part_five]

/-- The terminal part is also the old depth-five-minus-depth-six layer.
Only the absence of nonzero rational depth-six points is used. -/
theorem part_five_eq_layer (h : Geometry F f) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    part f ⟨5,by decide⟩ = (MicrolocalPromotedPartition.filtration f 5 \
      MicrolocalPromotedPartition.filtration f 6) \ {0} := by
  ext x
  simp only [part_five,MicrolocalPromotedPartition.filtration,show (5:ℕ)≠0 by decide,
    show (6:ℕ)≠0 by decide,if_false,Set.mem_diff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx,hn⟩
    exact ⟨⟨hx,MicrolocalTerminalPrimeCertificate.rational_not_mem_depth_six
      F hF hAn f h x hn⟩,hn⟩
  · exact fun hx => ⟨hx.1.1,hx.2⟩

/-- Every rational vector, including the origin, belongs to one and only
one of the seven actual parts. -/
theorem existsUnique_level (x : Fin 10 → ℚ) : ∃! j : Fin 7, x ∈ part f j := by
  by_cases hx : x=0
  · subst x
    refine ⟨⟨6,by decide⟩,?_,?_⟩
    · change (0 : Fin 10 → ℚ) ∈ part f ⟨6,by decide⟩
      rw [part_six]
      rfl
    intro j hj
    apply Fin.ext
    change j.val=6
    by_cases hj6 : j.val < 6
    · rw [part_of_lt_six j hj6] at hj
      exact (hj.2 rfl).elim
    · omega
  · obtain ⟨j,hj,huniq⟩ := MicrolocalPromotedPartition.existsUnique_level emptyPromotion
      (empty_compatible f) x hx
    refine ⟨⟨j.val,by omega⟩,?_,?_⟩
    · change x ∈ part f ⟨j.val,by omega⟩
      rw [part_of_lt_six _ j.isLt]
      exact hj
    · intro k hk
      by_cases hk6 : k.val<6
      · rw [part_of_lt_six k hk6] at hk
        have he := huniq ⟨k.val,hk6⟩ hk
        exact Fin.ext (congrArg (fun z : Fin 6 => z.val) he)
      · have he : k=(⟨6,by decide⟩ : Fin 7) := by
          apply Fin.ext
          change k.val=6
          omega
        rw [he,part_six] at hk
        exact (hx hk).elim

theorem union_parts : (⋃ j : Fin 7, part f j) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨j,hj,_⟩ := existsUnique_level (f:=f) x
  exact Set.mem_iUnion.mpr ⟨j,hj⟩

/-- Nonzero rational scaling preserves every part, including the origin. -/
theorem part_smul_mem_iff (h : Geometry F f) (j : Fin 7)
    (a : ℚ) (ha : a≠0) (x : Fin 10 → ℚ) :
    a • x ∈ part f j ↔ x ∈ part f j := by
  by_cases hj : j.val<6
  · rw [part_of_lt_six j hj]
    exact HomogeneousPromotionScaling.part_smul_mem_iff h emptyPromotion
      (fun _ _ _ _ hx => hx.elim) ⟨j.val,hj⟩ a ha x
  · simp only [part,dif_neg hj,Set.mem_singleton_iff,smul_eq_zero,ha,false_or]

/-- The origin contributes at most one literal integer point. -/
theorem origin_count_le_one (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ) (b : Fin 10 → ℤ) :
    ((points ({0} : Set (Fin 10 → ℚ)) u L m b).card : ℝ) ≤ 1 := by
  have hc : (points ({0} : Set (Fin 10 → ℚ)) u L m b).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hzero (z : Fin 10 → ℤ) (hz : z ∈ points ({0} : Set (Fin 10 → ℚ)) u L m b) :
        z=0 := by
      have hq : (fun a => (z a : ℚ))=0 := (mem_points _ _ _ _ _ _).mp hz |>.2.2
      ext a
      have ha : (z a : ℚ)=0 := congrFun hq a
      exact_mod_cast ha
    exact (hzero x hx).trans (hzero y hy).symm
  exact_mod_cast hc

private theorem exists_level_bound (h : Geometry F f) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) (j : Fin 7) :
    ∃ C : ℝ, 1≤C ∧ ∀ (u : Fin 10 → ℝ) (L : ℝ), 0≤L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
      ((points (part f j) u L m b).card : ℝ) ≤ C*(1+L/(m : ℝ))^(exponent j) := by
  by_cases hj0 : j.val=0
  · obtain ⟨C,hC,hbound⟩ := AmbientProgressionCount.exists_ten_bound
    exact ⟨C,hC,by simpa only [exponent,if_pos hj0] using hbound (part f j)⟩
  by_cases hj5 : j.val<5
  · have hd : affineDimension (rationalDepth f j.val) ≤ ((9-j.val : ℕ) : Dimension) := by
      simpa only [show 10-(j.val+1)=9-j.val by omega] using
        rationalDepth_dimension_le h hAn (j:=j.val) (by omega) (by omega)
    obtain ⟨C,hC,hbound⟩ := MicrolocalPromotedPartition.exists_ordinary_part_bound h hAn
      ⟨j.val,by omega⟩ (by change 0 < j.val; omega) (9-j.val) hd
    refine ⟨C,hC,?_⟩
    simpa only [part_of_lt_six j (by omega),exponent,if_neg hj0,if_pos hj5] using
      hbound emptyPromotion (empty_compatible f)
  by_cases hjeq : j.val=5
  · have he : j=(⟨5,by decide⟩ : Fin 7) := Fin.ext hjeq
    subst j
    obtain ⟨C,hC,hbound⟩ := MicrolocalPromotedPartition.exists_terminal_bound h hF hAn
    refine ⟨C,hC,?_⟩
    simpa only [part_of_lt_six ⟨5,by decide⟩ (by decide),exponent,show ¬(5:ℕ)=0 by decide,
      show ¬(5:ℕ)<5 by decide,if_false,if_true,pow_one] using
      hbound emptyPromotion (empty_compatible f)
  · have he : j=(⟨6,by decide⟩ : Fin 7) := by
      apply Fin.ext
      change j.val=6
      omega
    subst j
    refine ⟨1,le_rfl,?_⟩
    intro u L hL m hm b
    simpa [exponent] using origin_count_le_one u L m b

/-- One constant precedes all seven levels and all box/progression data.
The result is stronger than the source's H^epsilon version. -/
theorem exists_uniform_bound (h : Geometry F f) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1≤C ∧ ∀ (j : Fin 7) (u : Fin 10 → ℝ) (L : ℝ), 0≤L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
      ((points (part f j) u L m b).card : ℝ) ≤ C*(1+L/(m : ℝ))^(exponent j) := by
  classical
  choose C hC hbound using exists_level_bound h hF hAn
  have hnonneg : ∀ j, 0≤C j := fun j => (by norm_num : (0:ℝ)≤1).trans (hC j)
  have hsum : 0≤∑j,C j := Finset.sum_nonneg (fun j _ => hnonneg j)
  refine ⟨1+∑j,C j,by linarith,?_⟩
  intro j u L hL m hm b
  have hCj : C j ≤ 1+∑k,C k := by
    have hs := Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ j)
    linarith
  exact (hbound j u L hL m hm b).trans
    (mul_le_mul_of_nonneg_right hCj (by positivity))

/-- Source-shaped count with a common constant before all seven levels. -/
theorem exists_source_bound (h : Geometry F f) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1≤C ∧ ∀ (j : Fin 7) (u : Fin 10 → ℝ) (L : ℝ), 0≤L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
      ((points (part f j) u L m b).card : ℝ) ≤
        C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^(exponent j) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_bound h hF hAn
  refine ⟨C,hC,?_⟩
  intro j u L hL m hm b
  have hH : 1≤2+‖u‖+L+(m : ℝ) := by
    linarith [norm_nonneg u,Nat.cast_nonneg (α:=ℝ) m]
  have hr := Real.one_le_rpow hH hε.le
  exact (hbound j u L hL m hm b).trans
    (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hr) (by positivity))

end CubicTenVariables.MicrolocalSquarePartition
