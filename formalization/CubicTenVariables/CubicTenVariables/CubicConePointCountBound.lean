import CubicTenVariables.Literature.FiniteFieldPointCounts
import CubicTenVariables.AffineConePointCount
import CubicTenVariables.ReducedConeCoordinates

/-! Browning's generic point-count input propagates through an actual affine
cone decomposition. Constants are selected before the field, coefficients,
vertex dimension and complement. The decomposition is literal linear algebra;
no ten-variable exponential-sum estimate is an input. -/

set_option autoImplicit false

noncomputable section
namespace CubicTenVariables.CubicConePointCountBound
open MvPolynomial HessianTheorem11 Literature
open scoped BigOperators

/-- A finite maximum makes Browning's constant uniform over all complement
dimensions up to the fixed ambient number of variables. -/
theorem exists_uniform_base_bound (input : BrowningCubicPointCount) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m : ℕ, m ≤ n → 4 ≤ m →
      ∀ (K : Type) [Field K] [Fintype K] (Q : MvPolynomial (Fin m) K),
      (2 : K) ≠ 0 → (3 : K) ≠ 0 → Q.IsHomogeneous 3 →
      GeometricallyIntegralForm Q → GeometricallyNonconicalCubic Q →
      |(affineZeroCount Q : ℝ)-(Fintype.card K : ℝ)^(m-1)| ≤
        C*((Fintype.card K : ℝ)-1)*(Fintype.card K : ℝ)^((m : ℝ)-3) := by
  classical
  have hex (m : Fin (n+1)) : ∃ C : ℝ, 1 ≤ C ∧ (4 ≤ m.val →
      ∀ (K : Type) [Field K] [Fintype K] (Q : MvPolynomial (Fin m.val) K),
      (2 : K) ≠ 0 → (3 : K) ≠ 0 → Q.IsHomogeneous 3 →
      GeometricallyIntegralForm Q → GeometricallyNonconicalCubic Q →
      |(affineZeroCount Q : ℝ)-(Fintype.card K : ℝ)^(m.val-1)| ≤
        C*((Fintype.card K : ℝ)-1)*(Fintype.card K : ℝ)^((m.val : ℝ)-3)) := by
    by_cases hm : 4 ≤ m.val
    · obtain ⟨C,hC,hb⟩ := input m.val hm
      exact ⟨C,hC,fun _ => hb⟩
    · exact ⟨1,le_rfl,fun h => (hm h).elim⟩
  choose c hc hb using hex
  have hc0 (m) : 0 ≤ c m := zero_le_one.trans (hc m)
  refine ⟨1+∑i,c i,?_,?_⟩
  · have := Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => hc0 i)
    linarith
  · intro m hmn hm K _ _ Q h2 h3 hQ hI hN
    let j : Fin (n+1) := ⟨m,by omega⟩
    have hbound := hb j hm K Q h2 h3 hQ hI hN
    have hj : c j ≤ 1+∑i,c i := by
      have := Finset.single_le_sum (fun i (_ : i∈Finset.univ) => hc0 i)
        (Finset.mem_univ j)
      linarith
    have hq : 1 ≤ (Fintype.card K : ℝ) := by
      exact_mod_cast (Fintype.card_pos (α := K))
    exact hbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hj (sub_nonneg.mpr hq)) (Real.rpow_nonneg (by positivity) _))

/-- Exact cancellation of the vertex factor with the missing base variables. -/
theorem cone_error_le (q C NF NQ : ℝ) (r m n : ℕ)
    (hq : 0 < q) (hm : 1 ≤ m) (hrm : r+m=n)
    (hcount : NF=q^r*NQ)
    (hbase : |NQ-q^(m-1)| ≤ C*(q-1)*q^((m : ℝ)-3)) :
    |NF-q^(n-1)| ≤ C*(q-1)*q^((n : ℝ)-3) := by
  have hnat : r+(m-1)=n-1 := by omega
  have hreal : (r : ℝ)+(m : ℝ)=(n : ℝ) := by exact_mod_cast hrm
  calc
    |NF-q^(n-1)| = q^r*|NQ-q^(m-1)| := by
      rw [hcount,←hnat,pow_add,←mul_sub,abs_mul,abs_of_nonneg (by positivity)]
    _ ≤ q^r*(C*(q-1)*q^((m : ℝ)-3)) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = C*(q-1)*(q^r*q^((m : ℝ)-3)) := by ring
    _ = C*(q-1)*q^((n : ℝ)-3) := by
      rw [←Real.rpow_natCast q r,←Real.rpow_add hq]
      congr 2
      linarith

/-- An actual linear cone decomposition inherits Browning's exponent in the
original number of variables, with one constant for every allowed base. -/
theorem exists_uniform_decomposition_bound (input : BrowningCubicPointCount) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Type) [Field K] [Fintype K]
      (r m : ℕ), r+m=n → 4 ≤ m →
      ∀ (F : MvPolynomial (Fin n) K) (Q : MvPolynomial (Fin m) K)
      (E : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin m → K))),
      (∀x,eval x F=eval (E x).2 Q) →
      (2 : K)≠0 → (3 : K)≠0 → Q.IsHomogeneous 3 →
      GeometricallyIntegralForm Q → GeometricallyNonconicalCubic Q →
      |(affineZeroCount F : ℝ)-(Fintype.card K : ℝ)^(n-1)| ≤
        C*((Fintype.card K : ℝ)-1)*(Fintype.card K : ℝ)^((n : ℝ)-3) := by
  obtain ⟨C,hC,hb⟩ := exists_uniform_base_bound input n
  refine ⟨C,hC,?_⟩
  intro K _ _ r m hrm hm F Q E he h2 h3 hQ hI hN
  have hcount : (affineZeroCount F : ℝ)=
      (Fintype.card K : ℝ)^r*(affineZeroCount Q : ℝ) := by
    have h := AffineConePointCount.zero_card F Q E he
    simp only [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  exact cone_error_le _ C _ _ r m n (by positivity) (by omega) hrm hcount
    (hb m (by omega) hm K Q h2 h3 hQ hI hN)

/-- A sufficiently small actual maximal vertex gives the full cubic bound.
The minimal cone base, its geometric integrality, its nonconicality and the
exact zero-count factorization are all constructed in Lean. The only
literature premise is Browning's general nonconical cubic theorem. -/
theorem exists_uniform_bound (input : BrowningCubicPointCount) (n : ℕ) (hn : 4 ≤ n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3),
      (2 : K)≠0 → (3 : K)≠0 → GeometricallyIntegralForm F →
      Module.finrank K (ReducedCubicVertex.affineVertex F hF) ≤ n-4 →
      |(affineZeroCount F : ℝ)-(Fintype.card K : ℝ)^(n-1)| ≤
        C*((Fintype.card K : ℝ)-1)*(Fintype.card K : ℝ)^((n : ℝ)-3) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_decomposition_bound input n
  refine ⟨C,hC,?_⟩
  intro K _ _ F hF h2 h3 hI hv
  obtain ⟨E,Q,hQ,_hE,_hQeq,hfactor,heval,hvertex⟩ :=
    ReducedConeCoordinates.exists_cone_coordinates F hF h2 h3
  have hQI : GeometricallyIntegralForm Q := by
    constructor
    · intro hzero
      apply hI.1
      rw [hfactor,hzero]
      simp [PolynomialRestriction.restrict]
    · exact ReducedConeCoordinates.quotient_domain_baseChange_of_factor
        F Q (ReducedConeCoordinates.projection E) (ReducedConeCoordinates.sectionMatrix E)
        (ReducedConeCoordinates.projection_section E) hfactor hI.2
  have hQN : GeometricallyNonconicalCubic Q :=
    ReducedConeCoordinates.translation_baseChange_eq_zero Q hQ h2 hvertex
  exact hbound K _ _ (by omega) (by omega) F Q E heval h2 h3 hQ hQI hQN

end CubicTenVariables.CubicConePointCountBound
