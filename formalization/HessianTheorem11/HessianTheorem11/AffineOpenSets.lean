import HessianTheorem11.Concentration

/-! Elementary operations on actual relatively open subsets. Their density
on irreducible affine sets is proved directly from prime vanishing ideals. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial

theorem AlgebraicallyClosedSet.union {σ : Type*} {A B : Set (σ → GeometricField)}
    (hA : AlgebraicallyClosedSet A) (hB : AlgebraicallyClosedSet B) :
    AlgebraicallyClosedSet (A ∪ B) := by
  apply Set.Subset.antisymm _ (subset_geometricClosure _)
  intro x hx
  by_contra h
  have ha : x ∉ A := fun ha => h (Or.inl ha)
  have hb : x ∉ B := fun hb => h (Or.inr hb)
  have hfa : ∃ f ∈ vanishingIdeal GeometricField A, eval x f ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact ha (hA ▸ hn)
  have hfb : ∃ f ∈ vanishingIdeal GeometricField B, eval x f ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hb (hB ▸ hn)
  obtain ⟨f,hf,hfx⟩ := hfa
  obtain ⟨g,hg,hgx⟩ := hfb
  have hp : f*g ∈ vanishingIdeal GeometricField (A ∪ B) := by
    intro y hy
    rcases hy with hy|hy
    · change eval y (f*g)=0
      rw [map_mul,show eval y f=0 from hf y hy,zero_mul]
    · change eval y (f*g)=0
      rw [map_mul,show eval y g=0 from hg y hy,mul_zero]
  have hz := hx (f*g) hp
  exact (mul_ne_zero hfx hgx) (by simpa using hz)

theorem RelativelyOpenSet.inter {σ : Type*} {U A B : Set (σ → GeometricField)}
    (hA : RelativelyOpenSet U A) (hB : RelativelyOpenSet U B) :
    RelativelyOpenSet U (A ∩ B) := by
  obtain ⟨C,hC,rfl⟩ := hA
  obtain ⟨D,hD,rfl⟩ := hB
  exact ⟨C∪D,hC.union hD,by ext x; simp only [Set.mem_inter_iff,Set.mem_diff,Set.mem_union]; tauto⟩

theorem RelativelyOpenSet.dense_of_nonempty {σ : Type*}
    {U O : Set (σ → GeometricField)} (hU : AlgebraicallyClosedSet U)
    (hirred : GeometricallyIrreducible U) (hO : RelativelyOpenSet U O)
    (hne : O.Nonempty) : geometricClosure O = U := by
  obtain ⟨C,hC,rfl⟩ := hO
  apply Set.Subset.antisymm (geometricClosure_subset_closed Set.diff_subset hU)
  intro x hx p hp
  obtain ⟨y,hyU,hyC⟩ := hne
  have hex : ∃ g ∈ vanishingIdeal GeometricField C, eval y g ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hyC (hC ▸ hn)
  obtain ⟨g,hg,hgy⟩ := hex
  have hgnot : g ∉ vanishingIdeal GeometricField U := fun hh => hgy (hh y hyU)
  have hpg : p*g ∈ vanishingIdeal GeometricField U := by
    intro z hz
    by_cases hc : z∈C
    · change eval z (p*g)=0
      rw [map_mul,show eval z g=0 from hg z hc,mul_zero]
    · change eval z (p*g)=0
      rw [map_mul,show eval z p=0 from hp z ⟨hz,hc⟩,zero_mul]
  exact ((hirred.mem_or_mem hpg).resolve_right hgnot) x hx

theorem dense_open_inter_complement_nonempty {σ : Type*}
    {U O C : Set (σ → GeometricField)} (hdense : geometricClosure O = U)
    (hC : AlgebraicallyClosedSet C) (hnot : ¬ U ⊆ C) :
    (O ∩ (U \ C)).Nonempty := by
  by_contra hn
  have hsub : O ⊆ C := by
    intro x hx
    by_contra hc
    apply hn
    exact ⟨x,hx,hdense ▸ subset_geometricClosure O hx,hc⟩
  exact hnot (hdense ▸ geometricClosure_subset_closed hsub hC)

def GenericRankOpen.restrictOpen {n m a b : ℕ} {U : Set (GeometricPoint n)}
    {P : Fin m → GeometricPolynomial n}
    {M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField}
    (G : GenericRankOpen U P M) (O : Set (GeometricPoint n))
    (hO : RelativelyOpenSet U O) (hOG : O ⊆ G.openSet)
    (hdense : geometricClosure O = U) (hne : O.Nonempty) : GenericRankOpen U P M :=
  { G with
    openSet := O
    isOpen := hO
    subset := hOG.trans G.subset
    dense := hdense
    nonempty := hne
    smooth := fun x hx => G.smooth x (hOG hx)
    differential_rank := fun x hx => G.differential_rank x (hOG hx)
    kernel_dimension := fun x hx => G.kernel_dimension x (hOG hx)
    maximal_rank := fun x hx => G.maximal_rank x (hOG hx) }

end HessianTheorem11
