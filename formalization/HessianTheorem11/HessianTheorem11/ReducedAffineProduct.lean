import HessianTheorem11.AffineOpenSets
import Mathlib.Algebra.MvPolynomial.Funext

/-! Irreducibility of a product with affine space, proved from actual
polynomial specializations and primality of the base vanishing ideal.
No product, vector-bundle, component, or dimension input is used. -/
noncomputable section
namespace HessianTheorem11.ReducedAffineProduct
open MvPolynomial

variable {σ τ : Type*}

def affineProduct (Z : Set (σ → GeometricField)) : Set ((σ ⊕ τ) → GeometricField) :=
  {p | p ∘ Sum.inl ∈ Z}

def leftSpecialize (p : MvPolynomial (σ ⊕ τ) GeometricField) (v : τ → GeometricField) :
    MvPolynomial σ GeometricField := aeval (Sum.elim X (C ∘ v)) p

def rightSpecialize (p : MvPolynomial (σ ⊕ τ) GeometricField) (x : σ → GeometricField) :
    MvPolynomial τ GeometricField := aeval (Sum.elim (C ∘ x) X) p

@[simp] theorem eval_leftSpecialize (p : MvPolynomial (σ ⊕ τ) GeometricField)
    (x : σ → GeometricField) (v : τ → GeometricField) :
    eval x (leftSpecialize p v) = eval (Sum.elim x v) p := by
  rw [leftSpecialize, ← eval_polynomialMap]
  congr 1
  ext (i|j) <;> simp [polynomialMap]

@[simp] theorem eval_rightSpecialize (p : MvPolynomial (σ ⊕ τ) GeometricField)
    (x : σ → GeometricField) (v : τ → GeometricField) :
    eval v (rightSpecialize p x) = eval (Sum.elim x v) p := by
  rw [rightSpecialize, ← eval_polynomialMap]
  congr 1
  ext (i|j) <;> simp [polynomialMap]

theorem affineProduct_nonempty {Z : Set (σ → GeometricField)} (h : Z.Nonempty) :
    (affineProduct (τ := τ) Z).Nonempty := by
  obtain ⟨x,hx⟩ := h
  exact ⟨Sum.elim x 0,hx⟩

/-- Products with affine space preserve actual prime vanishing ideals. -/
theorem affineProduct_irreducible (Z : Set (σ → GeometricField))
    (hi : GeometricallyIrreducible Z) :
    GeometricallyIrreducible (affineProduct (τ := τ) Z) := by
  classical
  refine ⟨?_,?_⟩
  · intro htop
    obtain ⟨p,hp⟩ := affineProduct_nonempty (τ := τ) hi.nonempty
    have h1 : (1 : MvPolynomial (σ ⊕ τ) GeometricField) ∈
        vanishingIdeal GeometricField (affineProduct Z) := by rw [htop]; trivial
    have h := h1 p hp
    simp at h
  · intro f g hfg
    by_cases hf : f ∈ vanishingIdeal GeometricField (affineProduct Z)
    · exact Or.inl hf
    right
    have hex : ∃ p ∈ affineProduct Z, eval p f ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hf hn
    obtain ⟨p,hp,hpf⟩ := hex
    let f0 := leftSpecialize f (p ∘ Sum.inr)
    have hf0 : f0 ∉ vanishingIdeal GeometricField Z := by
      intro hh
      have h := hh (p ∘ Sum.inl) hp
      change eval (p ∘ Sum.inl) f0 = 0 at h
      apply hpf
      simpa only [f0, eval_leftSpecialize, Sum.elim_comp_inl_inr] using h
    intro q hq
    let v := q ∘ Sum.inr
    have hprod : f0 * leftSpecialize g v ∈ vanishingIdeal GeometricField Z := by
      intro x hx
      change eval x (f0 * leftSpecialize g v) = 0
      rw [map_mul]
      by_cases hz : eval x f0 = 0
      · rw [hz,zero_mul]
      have hfx : rightSpecialize f x ≠ 0 := by
        intro he
        apply hz
        change eval x (leftSpecialize f (p ∘ Sum.inr)) = 0
        rw [eval_leftSpecialize, ← eval_rightSpecialize, he, map_zero]
      have he : rightSpecialize f x * rightSpecialize g x = 0 := by
        apply MvPolynomial.funext
        intro w
        rw [map_mul, eval_rightSpecialize, eval_rightSpecialize, map_zero]
        simpa only [MvPolynomial.aeval_eq_eval, map_mul] using hfg (Sum.elim x w) hx
      have hgx := (mul_eq_zero.mp he).resolve_left hfx
      have hgv : eval x (leftSpecialize g v) = 0 := by
        rw [eval_leftSpecialize, ← eval_rightSpecialize g x v, hgx, map_zero]
      rw [hgv, mul_zero]
    have hg := (hi.mem_or_mem hprod).resolve_left hf0
    have h := hg (q ∘ Sum.inl) hq
    change eval (q ∘ Sum.inl) (leftSpecialize g v) = 0 at h
    change eval q g = 0
    simpa only [v, eval_leftSpecialize, Sum.elim_comp_inl_inr] using h

/-- Closure commutes with a product with the full affine factor. -/
theorem closure_affineProduct (Z : Set (σ → GeometricField)) :
    geometricClosure (affineProduct (τ := τ) Z) = affineProduct (geometricClosure Z) := by
  apply le_antisymm
  · intro p hp f hf
    have hvan : rename (Sum.inl : σ → σ ⊕ τ) f ∈
        vanishingIdeal GeometricField (affineProduct Z) := by
      intro q hq
      simpa only [MvPolynomial.aeval_eq_eval, eval_rename] using hf (q ∘ Sum.inl) hq
    have h := hp _ hvan
    simpa only [MvPolynomial.aeval_eq_eval, eval_rename] using h
  · intro p hp f hf
    have hvan : leftSpecialize f (p ∘ Sum.inr) ∈ vanishingIdeal GeometricField Z := by
      intro x hx
      change eval x (leftSpecialize f (p ∘ Sum.inr)) = 0
      rw [show eval x (leftSpecialize f (p ∘ Sum.inr)) =
        eval (Sum.elim x (p ∘ Sum.inr)) f from eval_leftSpecialize _ _ _]
      exact hf _ hx
    have hh := hp _ hvan
    change eval (p ∘ Sum.inl) (leftSpecialize f (p ∘ Sum.inr)) = 0 at hh
    change eval p f = 0
    simpa only [eval_leftSpecialize, Sum.elim_comp_inl_inr] using hh

end HessianTheorem11.ReducedAffineProduct
