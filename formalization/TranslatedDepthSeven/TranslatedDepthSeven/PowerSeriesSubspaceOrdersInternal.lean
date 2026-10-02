import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Data.Finset.Max

/-!
# Initial orders of a finite-dimensional power-series subspace

Distinct finite orders give linear independence.  Conversely, the
coefficients at all orders occurring in a subspace separate its vectors.
Hence the number of occurring orders is exactly the dimension.  These are
the elementary linear-algebra ingredients in the power-series proof of
the product-space inequality used for integral curves.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped PowerSeries

variable {K : Type*} [Field K]

theorem linearIndependent_powerSeries_of_distinct_orders
    {ι : Type*} (v : ι → PowerSeries K) (n : ι → ℕ)
    (hn : Function.Injective n) (hv : ∀ i, (v i).order = n i) :
    LinearIndependent K v := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hsum i hi
  by_contra hci
  let t := s.filter (fun j ↦ c j ≠ 0)
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image t n ht
  have hjc : c j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hjv : v j ≠ 0 := by
    intro hz
    have := hv j
    simp [hz] at this
  have hcoeff : PowerSeries.coeff (n j) (v j) ≠ 0 := by
    simpa [hv] using PowerSeries.coeff_order hjv
  have hsumcoeff := congrArg (PowerSeries.coeff (n j)) hsum
  have honly : (∑ k ∈ s, c k • PowerSeries.coeff (n j) (v k)) =
      c j • PowerSeries.coeff (n j) (v j) := by
    apply Finset.sum_eq_single j
    · intro k hk hkj
      by_cases hck : c k = 0
      · simp [hck]
      · have hkt : k ∈ t := Finset.mem_filter.mpr ⟨hk, hck⟩
        have hlt : n j < n k := lt_of_le_of_ne (hmin k hkt)
          (fun h ↦ hkj (hn h.symm))
        have hz := PowerSeries.coeff_of_lt_order (φ := v k) (n j)
          (by simpa [hv] using hlt)
        simp [hz]
    · intro hjs
      exact False.elim (hjs (Finset.mem_filter.mp hj).1)
  have hzero : c j * PowerSeries.coeff (n j) (v j) = 0 := by
    have honly' : (∑ k ∈ s, c k * PowerSeries.coeff (n j) (v k)) =
        c j * PowerSeries.coeff (n j) (v j) := by
      simpa only [smul_eq_mul] using honly
    simpa only [map_sum, map_smul, map_zero, smul_eq_mul, honly'] using hsumcoeff
  exact (mul_ne_zero hjc hcoeff) hzero

def powerSeriesSubspaceOrderSet (U : Submodule K (PowerSeries K)) : Set ℕ :=
  {n | ∃ f ∈ U, PowerSeries.order f = n}

theorem powerSeriesSubspaceOrderSet_finite
    (U : Submodule K (PowerSeries K)) [Module.Finite K U] :
    (powerSeriesSubspaceOrderSet U).Finite := by
  classical
  choose f hfU hf using
    (fun n : powerSeriesSubspaceOrderSet U ↦ n.property)
  let v : powerSeriesSubspaceOrderSet U → U := fun n ↦ ⟨f n, hfU n⟩
  have hv : LinearIndependent K v := by
    apply LinearIndependent.of_comp U.subtype
    exact linearIndependent_powerSeries_of_distinct_orders f (fun n ↦ n.1)
      Subtype.val_injective hf
  letI : Finite (powerSeriesSubspaceOrderSet U) := hv.finite_of_isNoetherian
  exact Set.toFinite _

theorem powerSeriesSubspaceOrderSet_ncard_eq_finrank
    (U : Submodule K (PowerSeries K)) [Module.Finite K U] :
    (powerSeriesSubspaceOrderSet U).ncard = Module.finrank K U := by
  classical
  let O := powerSeriesSubspaceOrderSet U
  letI : Fintype O := (powerSeriesSubspaceOrderSet_finite U).fintype
  choose f hfU hf using (fun n : O ↦ n.property)
  let v : O → U := fun n ↦ ⟨f n, hfU n⟩
  have hv : LinearIndependent K v := by
    apply LinearIndependent.of_comp U.subtype
    exact linearIndependent_powerSeries_of_distinct_orders f (fun n ↦ n.1)
      Subtype.val_injective hf
  have hlower : Fintype.card O ≤ Module.finrank K U := hv.fintype_card_le_finrank
  let c : U →ₗ[K] (O → K) :=
    { toFun := fun f n ↦ PowerSeries.coeff n.1 f.1
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hc : Function.Injective c := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro f hf
    change f = 0
    apply Subtype.ext
    by_contra hne
    let n := f.1.order.toNat
    have hn : f.1.order = (n : ℕ∞) := (PowerSeries.coe_toNat_order hne).symm
    have hO : n ∈ O := ⟨f.1, f.2, hn⟩
    have hcoeff := congrFun hf (⟨n, hO⟩ : O)
    exact PowerSeries.coeff_order hne hcoeff
  have hupper := LinearMap.finrank_le_finrank_of_injective hc
  have hupper' : Module.finrank K U ≤ Fintype.card O := by
    simpa using hupper
  simpa only [Module.finrank_pi_fintype, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Set.ncard_eq_toFinset_card', Set.toFinset_card] using
      Nat.le_antisymm hlower hupper'

end

end TranslatedDepthSeven
