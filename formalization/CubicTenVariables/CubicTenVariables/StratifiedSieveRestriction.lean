import CubicTenVariables.StratifiedCompositeSieve
import Mathlib.Data.Finset.Sort

/-! Ordered restrictions of literal sieve tuples and the finite multiplicity
of forgetting uniformly bounded modulus coordinates. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.StratifiedSieveRestriction
open MvPolynomial StratifiedSieveData
open scoped BigOperators
variable {n s : ℕ}

def index (A : Finset (Fin s)) : Fin A.card ↪o Fin s := A.orderEmbOfFin rfl

theorem index_mem (A : Finset (Fin s)) (i : Fin A.card) : index A i ∈ A :=
  A.orderEmbOfFin_mem rfl i

theorem exists_index (A : Finset (Fin s)) (i : Fin s) (hi : i ∈ A) :
    ∃ j, index A j = i := by
  exact ⟨(A.orderIsoOfFin rfl).symm ⟨i,hi⟩,
    congrArg Subtype.val ((A.orderIsoOfFin rfl).apply_symm_apply ⟨i,hi⟩)⟩

theorem prod_index (A : Finset (Fin s)) (g : Fin s → ℝ) :
    (∏ i, g (index A i)) = ∏ i ∈ A, g i := by
  calc
    _ = ∏ i : A, g i := (A.orderIsoOfFin rfl).toEquiv.prod_comp (fun i : A => g i)
    _ = _ := Finset.prod_coe_sort A g

def restrict (A : Finset (Fin s)) (p : (Fin s → ℕ) × (Fin n → ℤ)) :
    (Fin A.card → ℕ) × (Fin n → ℤ) := (fun i => p.1 (index A i),p.2)

theorem valid_restrict (A : Finset (Fin s)) (t : Fin s → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (U : Set (Fin n → ℤ)) (u : Fin n → ℝ) (L : ℝ) (m : ℕ)
    (b : Fin n → ℤ) (R : Fin s → ℝ) (p : (Fin s → ℕ) × (Fin n → ℤ))
    (hp : ValidTuple t G U u L m b R p) :
    ValidTuple (fun i => t (index A i)) (fun i => G (index A i)) U u L m b
      (fun i => R (index A i)) (restrict A p) := by
  refine ⟨(fun i => hp.squarefree _),?_,(fun i => hp.base_coprime _),
    hp.mem,hp.box,hp.progression,(fun i => hp.outside _),
    (fun i => hp.equations _),(fun i => hp.dyadic _)⟩
  intro i j hij
  exact hp.coprime ((index A).injective.ne hij)

/-- Every omitted coordinate lies in a fixed finite range. Keeping all
s slots in this auxiliary range avoids dependent complement indexing. -/
theorem card_le_restricted_card (A : Finset (Fin s)) (M : ℕ)
    (E : Finset ((Fin s → ℕ) × (Fin n → ℤ)))
    (hM : ∀ p ∈ E, ∀ i ∉ A, p.1 i ≤ M) :
    E.card ≤ (M+1)^s * (E.image (restrict A)).card := by
  classical
  let forget (p : (Fin s → ℕ) × (Fin n → ℤ)) : Fin s → ℕ :=
    fun i => if i ∈ A then 0 else p.1 i
  let F := Fintype.piFinset (fun _ : Fin s => Finset.range (M+1))
  have hcard := Finset.card_le_card_of_injOn
    (fun p => (forget p,restrict A p))
    (s := E) (t := F.product (E.image (restrict A))) ?_ ?_
  · simpa [F,Finset.card_product,Fintype.card_piFinset] using hcard
  · intro p hp
    apply Finset.mem_product.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_,Finset.mem_image_of_mem _ hp⟩
    intro i
    simp only [forget,Finset.mem_range]
    split_ifs with hi
    · omega
    · exact Nat.lt_succ_of_le (hM p hp i hi)
  · intro p hp q hq he
    have hf := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ A
      · obtain ⟨j,hj⟩ := exists_index A i hi
        simpa only [restrict,hj] using congrFun (congrArg Prod.fst hr) j
      · simpa only [forget,if_neg hi] using congrFun hf i
    · exact congrArg (fun z : (Fin A.card → ℕ) × (Fin n → ℤ) => z.2) hr

end CubicTenVariables.StratifiedSieveRestriction
