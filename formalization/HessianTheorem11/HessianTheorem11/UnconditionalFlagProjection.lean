import HessianTheorem11.FlagTransport
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Data.Finset.Max

/-! A hyperplane projection preserving a whole weighted-basis flag. This is
the dimension-reduction step for simultaneous splittings of two flags. All
maps and subspaces are actual linear algebra; no invariant theory input. -/
noncomputable section
namespace HessianTheorem11.UnconditionalFlags
open Module
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

def basisFlag (b : Basis ι K V) (w : ι → ℤ) (a : ℤ) : Submodule K V :=
  Submodule.span K {v | ∃ i, w i ≤ a ∧ v = b i}

theorem mem_basisFlag (b : Basis ι K V) (w : ι → ℤ) (i : ι) :
    b i ∈ basisFlag b w (w i) :=
  Submodule.subset_span ⟨i,le_rfl,rfl⟩

theorem basisFlag_mono (b : Basis ι K V) (w : ι → ℤ) : Monotone (basisFlag b w) := by
  intro a c hac
  apply Submodule.span_mono
  rintro x ⟨i,hi,rfl⟩
  exact ⟨i,hi.trans hac,rfl⟩

/-- The actual first level where a nonzero functional is visible. -/
theorem exists_first_visible (b : Basis ι K V) (w : ι → ℤ)
    (l : V →ₗ[K] K) (hl : l ≠ 0) :
    ∃ j, l (b j) ≠ 0 ∧ ∀ i, l (b i) ≠ 0 → w j ≤ w i := by
  classical
  have hex : ∃ i, l (b i) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hl
    apply b.ext
    intro i
    simpa using h i
  let s := Finset.univ.filter (fun i => l (b i) ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i,hi⟩ := hex
    exact ⟨i,by simp [s,hi]⟩
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image s w hs
  refine ⟨j,(Finset.mem_filter.mp hj).2,?_⟩
  intro i hi
  exact hmin i (by simp [s,hi])

/-- Earlier levels lie in the actual hyperplane kernel. -/
theorem basisFlag_le_ker_of_first_visible (b : Basis ι K V) (w : ι → ℤ)
    (l : V →ₗ[K] K) (j : ι)
    (hfirst : ∀ i, l (b i) ≠ 0 → w j ≤ w i) (a : ℤ) (ha : a < w j) :
    basisFlag b w a ≤ LinearMap.ker l := by
  apply Submodule.span_le.mpr
  rintro x ⟨i,hi,rfl⟩
  change l (b i) = 0
  by_contra h
  exact (not_lt_of_ge (hfirst i h)) (hi.trans_lt ha)

def hyperplaneProjection (l : V →ₗ[K] K) (v : V) : V →ₗ[K] V :=
  LinearMap.id - l.smulRight v

@[simp] theorem hyperplaneProjection_apply (l : V →ₗ[K] K) (v x : V) :
    hyperplaneProjection l v x = x - l x • v := rfl

theorem projection_mem_ker (l : V →ₗ[K] K) (v : V) (hv : l v = 1) (x : V) :
    hyperplaneProjection l v x ∈ LinearMap.ker l := by
  change l (x - l x • v) = 0
  simp [hv]

theorem projection_eq_self (l : V →ₗ[K] K) (v : V) (x : V)
    (hx : x ∈ LinearMap.ker l) : hyperplaneProjection l v x = x := by
  change l x = 0 at hx
  simp [hx]

/-- The first visible pivot yields a projection preserving every flag level,
not just one selected subspace. -/
theorem projection_preserves_flag (b : Basis ι K V) (w : ι → ℤ)
    (l : V →ₗ[K] K) (j : ι)
    (hfirst : ∀ i, l (b i) ≠ 0 → w j ≤ w i)
    (v : V) (hv : v ∈ basisFlag b w (w j)) :
    ∀ a x, x ∈ basisFlag b w a → hyperplaneProjection l v x ∈ basisFlag b w a := by
  intro a x hx
  by_cases ha : w j ≤ a
  · exact (basisFlag b w a).sub_mem hx
      ((basisFlag b w a).smul_mem _ (basisFlag_mono b w ha hv))
  · rw [projection_eq_self l v x (basisFlag_le_ker_of_first_visible b w l j
      hfirst a (lt_of_not_ge ha) hx)]
    exact hx

/-- An actual normalized pivot and retraction to ker(l), simultaneously
compatible with every level of the given weighted flag. -/
theorem exists_flagCompatible_projection (b : Basis ι K V) (w : ι → ℤ)
    (l : V →ₗ[K] K) (hl : l ≠ 0) :
    ∃ v : V, ∃ p : V →ₗ[K] V,
      l v = 1 ∧ p v = 0 ∧
      (∀ x, p x ∈ LinearMap.ker l) ∧
      (∀ x ∈ LinearMap.ker l, p x = x) ∧
      (∀ a x, x ∈ basisFlag b w a → p x ∈ basisFlag b w a) := by
  obtain ⟨j,hj,hfirst⟩ := exists_first_visible b w l hl
  let v := (l (b j))⁻¹ • b j
  have hv : l v = 1 := by simp [v,hj]
  have hvflag : v ∈ basisFlag b w (w j) :=
    (basisFlag b w (w j)).smul_mem _ (mem_basisFlag b w j)
  refine ⟨v,hyperplaneProjection l v,hv,?_,projection_mem_ker l v hv,
    fun x hx => projection_eq_self l v x hx,projection_preserves_flag b w l j hfirst v hvflag⟩
  simp [hv]

end HessianTheorem11.UnconditionalFlags
