import TranslatedDepthSeven.ProjectiveDegreeOneSurfaceLinearInternal
import TranslatedDepthSeven.RankSevenDegreeOneLineIncidence

/-!
# Hyperplanes through two points on an affine degree-one curve

There is a direct filtered-ring proof requiring no projective closure.
If a linear polynomial vanishes at two distinct points but is nonzero in
the domain coordinate ring, multiplication injects the degree-at-most-n
piece into the next piece.  Constants and one separating coordinate give
two independent extra directions, by the two point evaluations.  Thus the
Hilbert function grows by at least two at every step, contrary to its given
eventual slope one.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 2000000

/-- The linear growth obstruction before substituting the Hilbert
polynomial.  Its two evaluations are genuine zeroes of the prime ideal. -/
theorem affineHilbert_growth_two_of_linear_vanishes_at_two_points
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K)) (hprime : I.IsPrime)
    (x y : Fin N → K) (hx : x ∈ affineIdealZeroLocus I)
    (hy : y ∈ affineIdealZeroLocus I) (i : Fin N) (hxy : x i ≠ y i)
    (f : MvPolynomial (Fin N) K) (hdegree : f.totalDegree ≤ 1)
    (hfx : MvPolynomial.eval x f = 0) (hfy : MvPolynomial.eval y f = 0)
    (hf : f ∉ I) (n : ℕ) :
    Module.finrank K (affineHilbertFiltration K N I n) + 2 ≤
      Module.finrank K (affineHilbertFiltration K N I (n + 1)) := by
  letI : I.IsPrime := hprime
  let A := MvPolynomial (Fin N) K ⧸ I
  let q : MvPolynomial (Fin N) K →ₐ[K] A := Ideal.Quotient.mkₐ K I
  let F := affineHilbertFiltration K N I n
  let G := affineHilbertFiltration K N I (n + 1)
  have hfq : q f ≠ 0 := fun h ↦ hf (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hfm : q f ∈ quotientTotalDegreeFiltration K (Fin N) I 1 :=
    (mem_quotientTotalDegreeFiltration_iff K (Fin N) I 1 _).mpr ⟨f, hdegree, rfl⟩
  have hm (a : F) : q f * (a : A) ∈ G := by
    have h := mul_mem_quotientTotalDegreeFiltration K (Fin N) I hfm a.property
    simpa only [Nat.add_comm] using h
  have hc (c : K) : algebraMap K A c ∈ G := by
    exact (mem_quotientTotalDegreeFiltration_iff K (Fin N) I (n + 1) _).mpr
      ⟨C c, by simp, (Ideal.Quotient.mkₐ K I).commutes c⟩
  have hXm : q (X i) ∈ G := by
    exact (mem_quotientTotalDegreeFiltration_iff K (Fin N) I (n + 1) _).mpr
      ⟨X i, by rw [totalDegree_X]; omega, rfl⟩
  let L : (F × (K × K)) →ₗ[K] G :=
    { toFun v := ⟨q f * (v.1 : A) + algebraMap K A v.2.1 + v.2.2 • q (X i),
        G.add_mem (G.add_mem (hm v.1) (hc v.2.1)) (G.smul_mem v.2.2 hXm)⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
          map_add, add_smul, mul_add]
        abel
      map_smul' := by
        intro c a
        apply Subtype.ext
        change q f * (c • (a.1 : A)) + algebraMap K A (c * a.2.1) +
          (c * a.2.2) • q (X i) =
          c • (q f * (a.1 : A) + algebraMap K A a.2.1 + a.2.2 • q (X i))
        simp only [Algebra.smul_def, map_mul]
        ring }
  let ex : A →ₐ[K] K := affineIdealPointToQuotientAlgHom I ⟨x, hx⟩
  let ey : A →ₐ[K] K := affineIdealPointToQuotientAlgHom I ⟨y, hy⟩
  have hex (g : MvPolynomial (Fin N) K) : ex (q g) = MvPolynomial.eval x g := rfl
  have hey (g : MvPolynomial (Fin N) K) : ey (q g) = MvPolynomial.eval y g := rfl
  have hinjective : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hz : q f * (v.1 : A) + algebraMap K A v.2.1 + v.2.2 • q (X i) = 0 :=
      congrArg Subtype.val hv
    have h₀ := congrArg ex hz
    have h₁ := congrArg ey hz
    simp only [map_add, map_mul, map_smul, AlgHom.commutes,
      hex, hfx, zero_mul, zero_add, eval_X, map_zero, smul_eq_mul] at h₀
    simp only [map_add, map_mul, map_smul, AlgHom.commutes,
      hey, hfy, zero_mul, zero_add, eval_X, map_zero, smul_eq_mul] at h₁
    have hmul : v.2.2 * (x i - y i) = 0 := by
      linear_combination h₀ - h₁
    have hc0 : v.2.2 = 0 :=
      (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hxy)
    have hb0 : v.2.1 = 0 := by simpa only [hc0, zero_mul, add_zero] using h₀
    have ha0 : (v.1 : A) = 0 := by
      rw [hc0, hb0, map_zero, zero_smul, add_zero, add_zero] at hz
      exact (mul_eq_zero.mp hz).resolve_left hfq
    exact Prod.ext (Subtype.ext ha0) (Prod.ext hb0 hc0)
  have h := L.finrank_le_finrank_of_injective hinjective
  simpa only [Module.finrank_prod, Module.finrank_self, Nat.add_assoc] using h

/-- Every affine-linear equation vanishing at two distinct points of a
prime affine curve of degree one lies in its defining ideal. -/
theorem linear_mem_prime_of_affineHilbert_degree_one_of_two_points
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K))
    (hHilbert : HasAffineHilbertDimensionDegree I 1 1)
    (x y : Fin N → K) (hx : x ∈ affineIdealZeroLocus I)
    (hy : y ∈ affineIdealZeroLocus I) (hxy : x ≠ y)
    (f : MvPolynomial (Fin N) K) (hdegree : f.totalDegree ≤ 1)
    (hfx : MvPolynomial.eval x f = 0) (hfy : MvPolynomial.eval y f = 0) :
    f ∈ I := by
  by_contra hf
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  obtain ⟨hprime, _hd, P, hPdegree, hPlc, k₀, hPeventual⟩ := hHilbert
  have h := affineHilbert_growth_two_of_linear_vanishes_at_two_points
    I hprime x y hx hy i hi f hdegree hfx hfy hf k₀
  have hQ :
      (Module.finrank K (affineHilbertFiltration K N I k₀) : ℚ) + 2 ≤
        Module.finrank K (affineHilbertFiltration K N I (k₀ + 1)) := by
    exact_mod_cast h
  rw [hPeventual k₀ le_rfl, hPeventual (k₀ + 1) (by omega)] at hQ
  have hcoeff : P.coeff 1 = 1 := by
    simpa only [Polynomial.leadingCoeff, hPdegree, Nat.factorial_one,
      Nat.cast_one, div_one] using hPlc
  have hlinear (t : ℚ) : P.eval t = t + P.coeff 0 := by
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hPdegree.le]
    simp [hcoeff]
  rw [hlinear, hlinear] at hQ
  push_cast at hQ
  linarith

end

end TranslatedDepthSeven
