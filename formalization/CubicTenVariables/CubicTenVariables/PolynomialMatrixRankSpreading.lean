import CubicTenVariables.GenericEmptyFiberSpreading
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Spreading full row rank on a polynomial principal open

Failure of full row rank is represented by a nonzero row relation, with
one chart for each nonzero relation coordinate. A single inverse variable
enforces the principal-open condition and that coordinate's nonvanishing.
Nullstellensatz and the proved generic-empty-fiber theorem then supply one
nonzero base element before every field specialization. No minors or
effective elimination-degree bound is needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CubicTenVariables.PolynomialMatrixRankSpreading
open MvPolynomial
open scoped BigOperators

theorem fullRowRank_iff_no_row_relation
    {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (A : Matrix m n K) :
    A.rank = Fintype.card m ↔
      ∀ a : m → K, (∀ c, ∑ r, a r * A r c = 0) → a = 0 := by
  classical
  let T := Matrix.mulVecLin A.transpose
  have hmem (a : m → K) : a ∈ LinearMap.ker T ↔
      ∀ c, ∑ r, a r * A r c = 0 := by
    change A.transpose.mulVec a = 0 ↔ _
    simp only [funext_iff, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply]
    simp only [mul_comm]
  have hdim := T.finrank_range_add_finrank_ker
  change A.transpose.rank + Module.finrank K (LinearMap.ker T) =
    Module.finrank K (m → K) at hdim
  rw [Matrix.rank_transpose] at hdim
  simp only [Module.finrank_pi] at hdim
  constructor
  · intro hrank a ha
    have hker : LinearMap.ker T = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have h := (hmem a).mpr ha
    rwa [hker, Submodule.mem_bot] at h
  · intro h
    have hker : LinearMap.ker T = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro a ha
      change a = 0
      exact h a ((hmem a).mp ha)
    rw [hker, finrank_bot] at hdim
    simpa only [add_zero] using hdim

def evaluatedMatrix {B K σ m n : Type*} [CommRing B] [CommRing K]
    (ρ : B →+* K) (x : σ → K) (A : Matrix m n (MvPolynomial σ B)) : Matrix m n K :=
  fun r c ↦ eval₂Hom ρ x (A r c)

private def failureEquations {B σ τ m n : Type*} [CommRing B] [Fintype m]
    (G : τ → MvPolynomial σ B) (H : MvPolynomial σ B)
    (A : Matrix m n (MvPolynomial σ B)) (j : m) :
    τ ⊕ (n ⊕ Unit) → MvPolynomial (σ ⊕ (m ⊕ Unit)) B
  | Sum.inl e => rename Sum.inl (G e)
  | Sum.inr (Sum.inl c) => ∑ r, X (Sum.inr (Sum.inl r)) * rename Sum.inl (A r c)
  | Sum.inr (Sum.inr _) =>
      X (Sum.inr (Sum.inr ())) * rename Sum.inl H * X (Sum.inr (Sum.inl j)) - 1

private def failureIdeal {B σ τ m n : Type*} [CommRing B] [Fintype m]
    (G : τ → MvPolynomial σ B) (H : MvPolynomial σ B)
    (A : Matrix m n (MvPolynomial σ B)) (j : m) :
    Ideal (MvPolynomial (σ ⊕ (m ⊕ Unit)) B) :=
  Ideal.span (Set.range (failureEquations G H A j))

private theorem failureIdeal_map_eq_top
    {B Ω σ τ m n : Type*} [CommRing B] [Field Ω] [IsAlgClosed Ω]
    [Fintype σ] [Fintype τ] [Fintype m] [Fintype n]
    (ι : B →+* Ω) (G : τ → MvPolynomial σ B) (H : MvPolynomial σ B)
    (A : Matrix m n (MvPolynomial σ B))
    (hgeneric : ∀ x : σ → Ω, (∀ e, eval₂Hom ι x (G e) = 0) →
      eval₂Hom ι x H ≠ 0 → (evaluatedMatrix ι x A).rank = Fintype.card m)
    (j : m) : (failureIdeal G H A j).map (MvPolynomial.map ι) = ⊤ := by
  classical
  have hzero : zeroLocus Ω ((failureIdeal G H A j).map (MvPolynomial.map ι)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have he (e) : eval₂Hom ι y (failureEquations G H A j e) = 0 := by
      have h := hy (map ι (failureEquations G H A j e))
        (Ideal.mem_map_of_mem (MvPolynomial.map ι)
          (Ideal.subset_span (Set.mem_range_self e)))
      change eval y (map ι (failureEquations G H A j e)) = 0 at h
      simpa only [eval_map] using h
    let x : σ → Ω := fun s ↦ y (Sum.inl s)
    let a : m → Ω := fun r ↦ y (Sum.inr (Sum.inl r))
    have hG (e) : eval₂Hom ι x (G e) = 0 := by
      simpa [failureEquations, eval₂_rename, Function.comp_def, x] using he (Sum.inl e)
    have hnormal : y (Sum.inr (Sum.inr ())) * eval₂Hom ι x H * a j - 1 = 0 := by
      simpa [failureEquations, eval₂_rename, Function.comp_def, x, a] using
        he (Sum.inr (Sum.inr ()))
    have hH : eval₂Hom ι x H ≠ 0 := by
      intro hz
      simp [hz] at hnormal
    have haj : a j ≠ 0 := by
      intro hz
      simp [hz] at hnormal
    have hrow (c) : ∑ r, a r * evaluatedMatrix ι x A r c = 0 := by
      simpa [failureEquations, eval₂_rename, Function.comp_def, x, a,
        evaluatedMatrix] using he (Sum.inr (Sum.inl c))
    have ha := (fullRowRank_iff_no_row_relation _).mp (hgeneric x hG hH) a hrow
    exact haj (congrFun ha j)
  apply Ideal.radical_eq_top.mp
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := Ω), hzero, vanishingIdeal_empty]

private theorem no_solution_of_failureIdeal_map_top
    {B K σ τ m n : Type*} [CommRing B] [Field K] [Fintype m]
    (ρ : B →+* K) (G : τ → MvPolynomial σ B) (H : MvPolynomial σ B)
    (A : Matrix m n (MvPolynomial σ B)) (j : m)
    (htop : (failureIdeal G H A j).map (MvPolynomial.map ρ) = ⊤)
    (y : σ ⊕ (m ⊕ Unit) → K)
    (hy : ∀ e, eval₂Hom ρ y (failureEquations G H A j e) = 0) : False := by
  have hle : (failureIdeal G H A j).map (MvPolynomial.map ρ) ≤ RingHom.ker (eval y) := by
    rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro g ⟨e, rfl⟩
    change eval y (map ρ (failureEquations G H A j e)) = 0
    simpa only [eval_map] using hy e
  have h1 : (1 : MvPolynomial (σ ⊕ (m ⊕ Unit)) K) ∈
      (failureIdeal G H A j).map (MvPolynomial.map ρ) := by
    rw [htop]
    trivial
  have hz := hle h1
  exact one_ne_zero (by simpa only [RingHom.mem_ker, map_one] using hz)

/-- One actual nonzero base element makes the full-row-rank implication
hold after every coefficient specialization into every field. -/
theorem exists_nonzero_open
    {B Ω σ τ m n : Type*} [CommRing B] [IsDomain B]
    [Field Ω] [IsAlgClosed Ω]
    [Fintype σ] [Fintype τ] [Fintype m] [Fintype n]
    (ι : B →+* Ω) (hι : Function.Injective ι)
    (G : τ → MvPolynomial σ B) (H : MvPolynomial σ B)
    (A : Matrix m n (MvPolynomial σ B))
    (hgeneric : ∀ x : σ → Ω, (∀ e, eval₂Hom ι x (G e) = 0) →
      eval₂Hom ι x H ≠ 0 → (evaluatedMatrix ι x A).rank = Fintype.card m) :
    ∃ s : B, s ≠ 0 ∧ ∀ (K : Type*) [Field K] (ρ : B →+* K), ρ s ≠ 0 →
      ∀ x : σ → K, (∀ e, eval₂Hom ρ x (G e) = 0) →
        eval₂Hom ρ x H ≠ 0 → (evaluatedMatrix ρ x A).rank = Fintype.card m := by
  classical
  have hchart (j : m) := GenericEmptyFiberSpreading.exists_nonzero_open_of_injective
    (failureIdeal G H A j) ι hι (failureIdeal_map_eq_top ι G H A hgeneric j)
  choose s hs hgood using hchart
  refine ⟨∏ j, s j, Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hs j), ?_⟩
  intro K _ ρ hρ x hG hH
  apply (fullRowRank_iff_no_row_relation _).mpr
  intro a ha
  ext j
  by_contra haj
  have hprod : ∏ j, ρ (s j) ≠ 0 := by simpa only [map_prod] using hρ
  have hj : ρ (s j) ≠ 0 := Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j)
  let y : σ ⊕ (m ⊕ Unit) → K
    | Sum.inl t => x t
    | Sum.inr (Sum.inl r) => a r
    | Sum.inr (Sum.inr _) => (eval₂Hom ρ x H * a j)⁻¹
  apply no_solution_of_failureIdeal_map_top ρ G H A j (hgood j K ρ hj) y
  intro e
  rcases e with e | (c | u)
  · simpa [failureEquations, eval₂_rename, Function.comp_def, y] using hG e
  · simpa [failureEquations, eval₂_rename, Function.comp_def, y,
      evaluatedMatrix] using ha c
  · simp only [failureEquations, map_sub, map_mul, eval₂Hom_X', eval₂Hom_rename,
      map_one]
    change (eval₂Hom ρ x H * a j)⁻¹ * eval₂Hom ρ x H * a j - 1 = 0
    rw [mul_assoc, inv_mul_cancel₀ (mul_ne_zero hH haj), sub_self]

end CubicTenVariables.PolynomialMatrixRankSpreading
