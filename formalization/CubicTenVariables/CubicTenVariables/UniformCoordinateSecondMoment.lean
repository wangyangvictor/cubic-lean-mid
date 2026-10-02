import CubicTenVariables.BinarySliceExceptionalProved
import CubicTenVariables.BinarySliceSecondMoment
import CubicTenVariables.IntegralBinarySliceDegree
import CubicTenVariables.BinarySliceGeometricFiber
import CubicTenVariables.BinarySliceExceptional

/-! Uniformity over all finite extensions for the actual coordinate-plane
second moment. The one remaining geometric application hypothesis is an
explicit nonzero integer polynomial with geometrically integral good fibers. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.UniformCoordinateSecondMoment
open MvPolynomial BinarySliceCounting BinarySliceGeometry ProjectiveFourierIdentity
open HessianTheorem11
open scoped BigOperators Classical

theorem algebraicClosure_fiber {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (e : Fin 2 ↪ Fin n) (G : MvPolynomial (Complement e) ℤ)
    (hgood : ∀ (K : Type) [Field K] [IsAlgClosed K] (w : Complement e → K),
      eval₂ (Int.castRingHom K) w G ≠ 0 →
      IsDomain (MvPolynomial (Fin 2) K ⧸ Ideal.span {slice e (map (Int.castRingHom K) F) w}))
    (K : Type) [Field K] (w : Complement e → K)
    (hw : eval w (map (Int.castRingHom K) G) ≠ 0) :
    IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸ Ideal.span
      {map (algebraMap K (AlgebraicClosure K)) (slice e (map (Int.castRingHom K) F) w)}) := by
  let f := algebraMap K (AlgebraicClosure K)
  have hc : f.comp (Int.castRingHom K) = Int.castRingHom (AlgebraicClosure K) :=
    RingHom.ext_int _ _
  have hval : eval₂ (Int.castRingHom (AlgebraicClosure K)) (fun i => f (w i)) G ≠ 0 := by
    have hn : f (eval₂ (Int.castRingHom K) w G) ≠ 0 :=
      (map_ne_zero f).mpr (by simpa only [eval₂_eq_eval_map] using hw)
    simpa only [eval₂_comp_left, hc, Function.comp_def] using hn
  have hg := hgood (AlgebraicClosure K) (fun i => f (w i)) hval
  have he : map f (slice e (map (Int.castRingHom K) F) w) =
      slice e (map (Int.castRingHom (AlgebraicClosure K)) F) (fun i => f (w i)) := by
    rw [map_slice, MvPolynomial.map_map, hc]
  rw [show algebraMap K (AlgebraicClosure K) = f from rfl, he]
  exact hg

/-- The coefficient exclusions and moment constant are fixed before all
primes, finite extensions and nontrivial characters. In dimension ten the
right-hand exponent is exactly seventeen. -/
theorem exists_bound_of_exceptional (weil : Literature.AffinePlaneCubicWeil)
    {n : ℕ} (hn : 3 ≤ n) (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) (e : Fin 2 ↪ Fin n)
    (G : MvPolynomial (Complement e) ℤ) (hG : G ≠ 0)
    (hgood : ∀ (K : Type) [Field K] [IsAlgClosed K] (w : Complement e → K),
      eval₂ (Int.castRingHom K) w G ≠ 0 →
      IsDomain (MvPolynomial (Fin 2) K ⧸ Ideal.span {slice e (map (Int.castRingHom K) F) w})) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      ∀ (K : Type) [Field K] [Fintype K] [CharP K p] (ψ : AddChar K ℂ), ψ ≠ 1 →
        ∑ v ∈ Finset.univ.filter (fun v : Fin n → K => ∀ j : Fin 2, v (e j) = 0),
          ‖normalizedFourierSum ψ (map (Int.castRingHom K) F) v‖^2 ≤
            C*(Fintype.card K : ℝ)^(2*n-3) := by
  obtain ⟨B,hB,hbound⟩ := BinarySliceSecondMoment.exists_coordinate_bound weil
  obtain ⟨NG,hNG,hreduction⟩ := FiniteFieldPolynomialZeros.exists_uniform_nonzero_reduction G hG
  obtain ⟨NF,hNF,hdegree⟩ := IntegralBinarySliceDegree.exists_uniform_slice_degree F hF hA e
  have hGdeg : (0 : ℝ) ≤ (G.totalDegree : ℝ) := Nat.cast_nonneg _
  refine ⟨6*(NF*NG), one_le_mul_of_one_le_of_one_le (by decide)
      (one_le_mul_of_one_le_of_one_le hNF hNG),
    B+4*(G.totalDegree : ℝ), by linarith, ?_⟩
  intro p hp hN K _ _ _ ψ hψ
  have hpFG : ¬ p ∣ NF*NG := fun h => hN (dvd_mul_of_dvd_right h 6)
  have hpF : ¬ p ∣ NF := fun h => hpFG (dvd_mul_of_dvd_left h NG)
  have hpG : ¬ p ∣ NG := fun h => hpFG (dvd_mul_of_dvd_right h NF)
  have hp6 : ¬ p ∣ 6 := fun h => hN (dvd_mul_of_dvd_left h (NF*NG))
  have h2 : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K p 2).not.mpr
    (fun h => hp6 (dvd_trans h (by norm_num)))
  have h3 : (3 : K) ≠ 0 := (CharP.cast_eq_zero_iff K p 3).not.mpr
    (fun h => hp6 (dvd_trans h (by norm_num)))
  have hd (w : Complement e → K) :
      (slice e (map (Int.castRingHom K) F) w).totalDegree = 3 :=
    hdegree p hpF K w
  have h := hbound K h2 h3 n hn (map (Int.castRingHom K) F) (hF.map _).totalDegree_le
    e (map (Int.castRingHom K) G) (hreduction p hpG K) hd
    (fun w hw => algebraicClosure_fiber F e G hgood K w hw) ψ hψ
  apply h.trans
  have hdeg : ((map (Int.castRingHom K) G).totalDegree : ℝ) ≤ (G.totalDegree : ℝ) := by
    exact_mod_cast (Finset.sup_mono (support_map_subset (Int.castRingHom K) G))
  gcongr

/-- The geometric application is discharged for every rational anisotropic
cubic in at least four variables. The geometric inputs have internal proofs;
only the affine curve Weil bound remains an unproved literature premise. -/
theorem exists_bound (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil) {n : ℕ} (hn : 4 ≤ n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) (e : Fin 2 ↪ Fin n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      ∀ (K : Type) [Field K] [Fintype K] [CharP K p] (ψ : AddChar K ℂ), ψ ≠ 1 →
        ∑ v ∈ Finset.univ.filter (fun v : Fin n → K => ∀ j : Fin 2, v (e j) = 0),
          ‖normalizedFourierSum ψ (map (Int.castRingHom K) F) v‖^2 ≤
            C*(Fintype.card K : ℝ)^(2*n-3) := by
  obtain ⟨G,hG,hgood⟩ := BinarySliceExceptionalProved.exists_exceptional_polynomial_of_uniform spread hn e F hF hA
  exact exists_bound_of_exceptional weil (by omega) F hF hA e G hG hgood

end CubicTenVariables.UniformCoordinateSecondMoment
