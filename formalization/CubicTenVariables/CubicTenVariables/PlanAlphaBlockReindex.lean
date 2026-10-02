import CubicTenVariables.PlanAlphaBlockIndices

/-! Exact reindexing of arbitrary finite modulus-frequency samples by the
canonical mixed-modulus block and the cube-full factor. The original
sample restrictions are preserved by finite images, and reconstruction
proves that no summands are lost or counted twice. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.PlanAlphaBlockReindex
open PlanAlphaModulusDecomposition PlanAlphaBlockIndices
open scoped BigOperators
variable {α β : Type*} [DecidableEq α]

/-- Original samples with the selected canonical block index. -/
def blockFiber (s : Finset ℕ) (E : Finset (ℕ × α)) (b : ℕ × ℕ × ℕ) : Finset (ℕ × α) :=
  E.filter (fun x => blockIndex s x.1 = b)

/-- The actual cube-full factors occurring in the selected block. -/
def factors (s : Finset ℕ) (E : Finset (ℕ × α)) (b : ℕ × ℕ × ℕ) : Finset ℕ :=
  (blockFiber s E b).image (fun x => r s x.1)

/-- Original samples with both the block and cube-full factor fixed. -/
def factorFiber (s : Finset ℕ) (E : Finset (ℕ × α)) (b : ℕ × ℕ × ℕ) (c : ℕ) :
    Finset (ℕ × α) := (blockFiber s E b).filter (fun x => r s x.1 = c)

/-- The actual cube-free modulus and unchanged frequency in each fiber. -/
def samples (s : Finset ℕ) (E : Finset (ℕ × α)) (b : ℕ × ℕ × ℕ) (c : ℕ) :
    Finset (ℕ × α) := (factorFiber s E b c).image (fun x => (d s x.1,x.2))

theorem mem_factors_iff (s : Finset ℕ) (E : Finset (ℕ × α)) (b : ℕ × ℕ × ℕ) (c : ℕ) :
    c ∈ factors s E b ↔ ∃ x ∈ E, blockIndex s x.1 = b ∧ r s x.1 = c := by
  simp only [factors,blockFiber,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨x,⟨hx,hb⟩,hc⟩
    exact ⟨x,hx,hb,hc⟩
  · rintro ⟨x,hx,hb,hc⟩
    exact ⟨x,⟨hx,hb⟩,hc⟩

theorem mem_samples_iff (s : Finset ℕ) (E : Finset (ℕ × α))
    (b : ℕ × ℕ × ℕ) (c : ℕ) (y : ℕ × α) :
    y ∈ samples s E b c ↔
      ∃ x ∈ E, blockIndex s x.1 = b ∧ r s x.1 = c ∧ d s x.1 = y.1 ∧ x.2 = y.2 := by
  simp only [samples,factorFiber,blockFiber,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨x,⟨⟨hx,hb⟩,hc⟩,he⟩
    have hd := congrArg (fun z : ℕ × α => z.1) he
    have hv := congrArg (fun z : ℕ × α => z.2) he
    exact ⟨x,hx,hb,hc,hd,hv⟩
  · rintro ⟨x,hx,hb,hc,hd,hv⟩
    exact ⟨x,⟨⟨hx,hb⟩,hc⟩,Prod.ext hd hv⟩

/-- Reconstructing a transformed sample recovers an original sample and
its exact canonical factorization data. -/
theorem mem_samples_reconstructed (s : Finset ℕ) (E : Finset (ℕ × α))
    (hE : ∀ x ∈ E, 0 < x.1) (b : ℕ × ℕ × ℕ) (c : ℕ) (y : ℕ × α)
    (hy : y ∈ samples s E b c) :
    (b.1*y.1*c,y.2) ∈ E ∧ blockIndex s (b.1*y.1*c) = b ∧
      r s (b.1*y.1*c) = c ∧ d s (b.1*y.1*c) = y.1 := by
  obtain ⟨x,hx,hb,hc,hd,hv⟩ := (mem_samples_iff s E b c y).mp hy
  have hg : g s x.1 = b.1 := congrArg Prod.fst hb
  have hrec : x.1 = b.1*y.1*c := by rw [reconstruction s x.1 (hE x hx),hg,hc,hd]
  have he : x = (b.1*y.1*c,y.2) := Prod.ext hrec hv
  rw [← hrec]
  exact ⟨by simpa only [← hv] using hx,hb,hc,hd⟩

private theorem sum_factorFiber [AddCommMonoid β]
    (s : Finset ℕ) (E : Finset (ℕ × α)) (hE : ∀ x ∈ E, 0 < x.1)
    (b : ℕ × ℕ × ℕ) (c : ℕ) (f : ℕ → α → β) :
    (∑ x ∈ factorFiber s E b c, f x.1 x.2) =
      ∑ y ∈ samples s E b c, f (b.1*y.1*c) y.2 := by
  have hrec (x : ℕ × α) (hx : x ∈ factorFiber s E b c) :
      x.1 = b.1*d s x.1*c := by
    have hx' := Finset.mem_filter.mp hx
    have hb := (Finset.mem_filter.mp hx'.1).2
    have hg : g s x.1 = b.1 := congrArg Prod.fst hb
    calc
      x.1 = g s x.1*d s x.1*r s x.1 :=
        reconstruction s x.1 (hE x (Finset.mem_filter.mp hx'.1).1)
      _ = _ := by rw [hg,hx'.2]
  have hinj : Set.InjOn (fun x : ℕ × α => (d s x.1,x.2)) (factorFiber s E b c) := by
    intro x hx z hz he
    apply Prod.ext
    · have hd : d s x.1 = d s z.1 := congrArg (fun y : ℕ × α => y.1) he
      calc
        x.1 = b.1*d s x.1*c := hrec x hx
        _ = b.1*d s z.1*c := by rw [hd]
        _ = z.1 := (hrec z hz).symm
    · have hv := congrArg (fun y : ℕ × α => y.2) he
      exact hv
  rw [samples,Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro x hx
  exact congrArg (fun q => f q x.2) (hrec x hx)

/-- The exact finite block sum identity, valid for arbitrary additional
restrictions in E and for any additive commutative target monoid. -/
theorem sum_eq_blocks [AddCommMonoid β]
    (s : Finset ℕ) (E : Finset (ℕ × α)) (hE : ∀ x ∈ E, 0 < x.1)
    (f : ℕ → α → β) :
    (∑ x ∈ E, f x.1 x.2) =
      ∑ b ∈ E.image (fun x => blockIndex s x.1),
        ∑ c ∈ factors s E b, ∑ y ∈ samples s E b c, f (b.1*y.1*c) y.2 := by
  have hb : (∑ b ∈ E.image (fun x => blockIndex s x.1),
      ∑ x ∈ blockFiber s E b, f x.1 x.2) = ∑ x ∈ E, f x.1 x.2 := by
    have hm : ∀ x ∈ E, blockIndex s x.1 ∈ E.image (fun y => blockIndex s y.1) := by
      intro x hx
      exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
    simpa only [blockFiber] using
      Finset.sum_fiberwise_of_maps_to hm (fun x : ℕ × α => f x.1 x.2)
  rw [← hb]
  apply Finset.sum_congr rfl
  intro b _
  have hc : (∑ c ∈ factors s E b, ∑ x ∈ factorFiber s E b c, f x.1 x.2) =
      ∑ x ∈ blockFiber s E b, f x.1 x.2 := by
    have hm : ∀ x ∈ blockFiber s E b, r s x.1 ∈ factors s E b := by
      intro x hx
      exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
    simpa only [factorFiber] using
      Finset.sum_fiberwise_of_maps_to hm (fun x : ℕ × α => f x.1 x.2)
  rw [← hc]
  apply Finset.sum_congr rfl
  intro c _
  exact sum_factorFiber s E hE b c f

/-- The occupied block indices depend only on the actual modulus image,
so the already proved block-count estimate applies directly. -/
theorem occupied_indices_eq (s : Finset ℕ) (E : Finset (ℕ × α)) :
    E.image (fun x => blockIndex s x.1) = (E.image Prod.fst).image (blockIndex s) := by
  simp only [Finset.image_image,Function.comp_def]

end CubicTenVariables.PlanAlphaBlockReindex
