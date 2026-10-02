import CubicTenVariables.FirstLiftSum
import CubicTenVariables.PrimeSumAdapter
import CubicTenVariables.QuadraticGaussBound

/-! The actual prime-square sum is bounded by its exact stationary support.
For a nonzero reduced frequency, the scalar in a stationary pair is unique,
so the pair count is precisely the count of the corresponding Gauss points.
No point-count or literature premise is used. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.PrimeSquareStationaryBound
open MvPolynomial FirstLiftSum PrimeSumAdapter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Actual stationary pairs, including the equation of the hypersurface. -/
def stationaryPairs {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] [Fintype K] (v : Fin n → K) :
    Finset (K × (Fin n → K)) :=
  Finset.univ.filter fun z => z.1 ≠ 0 ∧
    eval₂ (Int.castRingHom K) z.2 F = 0 ∧
    ∀ i, z.1 * eval₂ (Int.castRingHom K) z.2 (pderiv i F) = -v i

/-- The point projection of the stationary support, with its scalar written
as a genuine existential quantifier over the same field. -/
def gaussPoints {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] [Fintype K] (v : Fin n → K) : Finset (Fin n → K) :=
  Finset.univ.filter fun y => eval₂ (Int.castRingHom K) y F = 0 ∧
    ∃ b : K, b ≠ 0 ∧ ∀ i, b * eval₂ (Int.castRingHom K) y (pderiv i F) = -v i

@[simp] theorem mem_stationaryPairs {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] [Fintype K] (v : Fin n → K) (z : K × (Fin n → K)) :
    z ∈ stationaryPairs F K v ↔ z.1 ≠ 0 ∧
      eval₂ (Int.castRingHom K) z.2 F = 0 ∧
      ∀ i, z.1 * eval₂ (Int.castRingHom K) z.2 (pderiv i F) = -v i := by
  simp [stationaryPairs]

@[simp] theorem mem_gaussPoints {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] [Fintype K] (v y : Fin n → K) :
    y ∈ gaussPoints F K v ↔ eval₂ (Int.castRingHom K) y F = 0 ∧
      ∃ b : K, b ≠ 0 ∧ ∀ i, b * eval₂ (Int.castRingHom K) y (pderiv i F) = -v i := by
  simp [gaussPoints]

/-- The integer divisibility conditions in the exact first lift reduce to
precisely the displayed equations over the prime field. -/
theorem supportCondition_iff {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) (a : Fin p) (y : Fin n → Fin p) (v : Fin n → ℤ) :
    supportCondition F p (a.val : ℤ) (fun i => ((y i).val : ℤ)) v ↔
      eval₂ (Int.castRingHom (ZMod p)) (fun i => ((y i).val : ZMod p)) F = 0 ∧
      ∀ i, (a.val : ZMod p) *
        eval₂ (Int.castRingHom (ZMod p)) (fun j => ((y j).val : ZMod p))
          (pderiv i F) = -(v i : ZMod p) := by
  unfold supportCondition
  simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, Int.cast_mul,
    Int.cast_natCast, cast_eval_fin, ← eval₂_eq_eval_map, add_eq_zero_iff_eq_neg]

private theorem card_stationaryPairs_eq {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ) :
    ((stationaryPairs F (ZMod p) (fun i => (v i : ZMod p))).card : ℝ) =
      ∑ a : Fin p, if Nat.Coprime a.val p then
        ∑ y : Fin n → Fin p,
          if supportCondition F p (a.val : ℤ) (fun i => ((y i).val : ℤ)) v
          then (1 : ℝ) else 0
      else 0 := by
  classical
  rw [Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, stationaryPairs, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  symm
  apply Fintype.sum_equiv (finResidueEquiv p)
  intro a
  simp only [finResidueEquiv_apply, coprime_prime_iff_residue_ne_zero]
  by_cases ha : (a.val : ZMod p) ≠ 0
  · rw [if_pos ha]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Fintype.sum_equiv (vectorResidueEquiv p n)
    intro y
    simp only [vectorResidueEquiv_apply, supportCondition_iff]
    congr 1
    exact propext (and_iff_right ha).symm
  · simp [ha]

/-- Exact first lifting plus the triangle inequality, with no supplied
lifting identity and no enlargement of the stationary support. -/
theorem norm_completeCubicSum_le_stationaryPairs {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ) :
    ‖completeCubicSum F (p^2) v‖ ≤ (p : ℝ)^(n+1) *
      ((stationaryPairs F (ZMod p) (fun i => (v i : ZMod p))).card : ℝ) := by
  classical
  rw [pow_two, completeCubicSum_firstLift F hF p p (dvd_refl p), norm_mul,
    norm_pow, Complex.norm_natCast, card_stationaryPairs_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold lowDigitSum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : Nat.Coprime a.val p
  · simp only [if_pos ha]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro y _
    split_ifs
    · simp only [residueExponential_eq_stdAddChar, QuadraticGaussBound.norm_stdAddChar]
      exact le_rfl
    · simp
  · simp [ha]

/-- For nonzero frequency a stationary point has nonzero gradient. -/
theorem gradient_ne_zero_of_mem {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] [Fintype K] (v : Fin n → K) (hv : v ≠ 0)
    (z : K × (Fin n → K)) (hz : z ∈ stationaryPairs F K v) :
    (fun i => eval₂ (Int.castRingHom K) z.2 (pderiv i F)) ≠ 0 := by
  intro hg
  apply hv
  funext i
  have hi := (mem_stationaryPairs F K v z).mp hz |>.2.2 i
  have hgi := congrFun hg i
  simp only [Pi.zero_apply] at hgi ⊢
  rw [hgi, mul_zero] at hi
  exact neg_eq_zero.mp hi.symm

/-- Projection forgets no multiplicity: its scalar is uniquely determined
by any nonzero coordinate of the gradient. -/
theorem snd_injOn_stationaryPairs {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] [Fintype K] (v : Fin n → K) (hv : v ≠ 0) :
    Set.InjOn Prod.snd (stationaryPairs F K v : Set (K × (Fin n → K))) := by
  intro z hz w hw hy
  have hg := gradient_ne_zero_of_mem F K v hv z hz
  obtain ⟨i, hi⟩ : ∃ i, eval₂ (Int.castRingHom K) z.2 (pderiv i F) ≠ 0 := by
    by_contra! h
    exact hg (funext h)
  apply Prod.ext _ hy
  apply mul_right_cancel₀ hi
  calc
    z.1 * eval₂ (Int.castRingHom K) z.2 (pderiv i F) = -v i :=
      ((mem_stationaryPairs F K v z).mp hz).2.2 i
    _ = w.1 * eval₂ (Int.castRingHom K) z.2 (pderiv i F) := by
      rw [hy]
      exact (((mem_stationaryPairs F K v w).mp hw).2.2 i).symm

theorem image_stationaryPairs {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] [Fintype K] (v : Fin n → K) :
    (stationaryPairs F K v).image Prod.snd = gaussPoints F K v := by
  classical
  ext y
  simp only [Finset.mem_image, mem_stationaryPairs, mem_gaussPoints]
  constructor
  · rintro ⟨⟨b,x⟩,⟨hb,hx,he⟩,rfl⟩
    exact ⟨hx,b,hb,he⟩
  · rintro ⟨hy,b,hb,he⟩
    exact ⟨(b,y),⟨hb,hy,he⟩,rfl⟩

theorem card_stationaryPairs_eq_gaussPoints {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] [Fintype K] (v : Fin n → K) (hv : v ≠ 0) :
    (stationaryPairs F K v).card = (gaussPoints F K v).card := by
  classical
  rw [← image_stationaryPairs]
  exact (Finset.card_image_of_injOn (snd_injOn_stationaryPairs F K v hv)).symm

/-- The requested prime-square bound by actual Gauss points. -/
theorem norm_completeCubicSum_le_gaussPoints {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ)
    (hv : (fun i => (v i : ZMod p)) ≠ 0) :
    ‖completeCubicSum F (p^2) v‖ ≤ (p : ℝ)^(n+1) *
      ((gaussPoints F (ZMod p) (fun i => (v i : ZMod p))).card : ℝ) := by
  rw [← card_stationaryPairs_eq_gaussPoints F (ZMod p) _ hv]
  exact norm_completeCubicSum_le_stationaryPairs F hF p v

end CubicTenVariables.PrimeSquareStationaryBound
