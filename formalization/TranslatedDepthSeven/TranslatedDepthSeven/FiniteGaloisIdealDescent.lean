import TranslatedDepthSeven.FiniteGaloisSubspaceDescent
import TranslatedDepthSeven.GaloisMinimalComponentFrontier

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators
open MvPolynomial

universe u v w

variable {K : Type u} {L : Type v} {σ : Type w}
  [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance : DecidableEq (L ≃ₐ[K] L) := Classical.decEq _

def finiteGaloisConjugatePolynomial (τ : L ≃ₐ[K] L) :
    MvPolynomial σ L ≃+* MvPolynomial σ L :=
  MvPolynomial.mapEquiv σ τ.toRingEquiv

def finiteGaloisConjugateIdeal (τ : L ≃ₐ[K] L)
    (J : Ideal (MvPolynomial σ L)) : Ideal (MvPolynomial σ L) :=
  J.map (finiteGaloisConjugatePolynomial τ).toRingHom

/-- The polynomial whose coefficients are the trace-dual descent
coefficients of `p`. -/
def galoisDescentPolynomial (p : MvPolynomial σ L) (τ : L ≃ₐ[K] L) :
    MvPolynomial σ K :=
  ∑ m ∈ p.support, MvPolynomial.monomial m
    (Algebra.trace K L (MvPolynomial.coeff m p *
      (IsGalois.normalBasis K L).traceDual τ))

theorem map_galoisDescentPolynomial
    (p : MvPolynomial σ L) (τ : L ≃ₐ[K] L) :
    MvPolynomial.map (algebraMap K L) (galoisDescentPolynomial p τ) =
      ∑ m ∈ p.support, MvPolynomial.monomial m
        (algebraMap K L (Algebra.trace K L
          (MvPolynomial.coeff m p *
            (IsGalois.normalBasis K L).traceDual τ))) := by
  classical
  rw [galoisDescentPolynomial]
  simp only [map_sum, MvPolynomial.map_monomial]

theorem coeff_galoisDescentPolynomial
    (p : MvPolynomial σ L) (τ : L ≃ₐ[K] L) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (galoisDescentPolynomial p τ) =
      Algebra.trace K L
        (MvPolynomial.coeff m p *
          (IsGalois.normalBasis K L).traceDual τ) := by
  classical
  rw [galoisDescentPolynomial, MvPolynomial.coeff_sum]
  by_cases hm : m ∈ p.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro i _ hne
      simp [hne]
    · exact fun h ↦ (h hm).elim
  · rw [Finset.sum_eq_zero]
    · rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul, map_zero]
    · intro i hi
      simp [show i ≠ m from fun h ↦ hm (h ▸ hi)]

theorem sum_normalBasis_smul_map_galoisDescentPolynomial
    (p : MvPolynomial σ L) :
    ∑ τ : L ≃ₐ[K] L, (IsGalois.normalBasis K L τ) •
      MvPolynomial.map (algebraMap K L) (galoisDescentPolynomial p τ) = p := by
  classical
  ext m
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_map, coeff_galoisDescentPolynomial]
  simpa using congrFun (sum_normalBasis_smul_galoisDescentCoefficient
    (K := K) (L := L) (w := fun m ↦ MvPolynomial.coeff m p)) m

/-- A Galois-stable ideal in `L[X]` is the coefficient extension of its
contraction to `K[X]`. -/
theorem map_comap_eq_of_finiteGalois_invariant
    (J : Ideal (MvPolynomial σ L))
    (hstable : ∀ τ : L ≃ₐ[K] L, finiteGaloisConjugateIdeal τ J = J) :
    (J.comap (MvPolynomial.map (algebraMap K L))).map
        (MvPolynomial.map (algebraMap K L)) = J := by
  apply le_antisymm
  · exact (Ideal.map_le_iff_le_comap).mpr le_rfl
  · intro p hp
    rw [← sum_normalBasis_smul_map_galoisDescentPolynomial (K := K) p]
    apply Ideal.sum_mem
    intro τ _
    rw [Algebra.smul_def]
    apply (J.comap (MvPolynomial.map (algebraMap K L))).map
      (MvPolynomial.map (algebraMap K L)) |>.mul_mem_left
    apply Ideal.mem_map_of_mem
    -- The mapped descended polynomial is a trace-weighted sum of conjugates;
    -- expand the trace and use Galois stability term by term.
    change MvPolynomial.map (algebraMap K L)
      (galoisDescentPolynomial p τ) ∈ J
    rw [show MvPolynomial.map (algebraMap K L)
          (galoisDescentPolynomial p τ) =
        ∑ g : L ≃ₐ[K] L,
          g ((IsGalois.normalBasis K L).traceDual τ) •
            finiteGaloisConjugatePolynomial g p by
      ext m
      simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
        MvPolynomial.coeff_map, coeff_galoisDescentPolynomial]
      simpa [finiteGaloisConjugatePolynomial, MvPolynomial.coeff_map] using
        congrFun (algebraMap_galoisDescentCoefficient_eq_sum_conjugates
          (K := K) (L := L)
          (w := fun m ↦ MvPolynomial.coeff m p) τ) m]
    apply Ideal.sum_mem
    intro g _
    rw [Algebra.smul_def]
    apply J.mul_mem_left
    have hg : finiteGaloisConjugatePolynomial g p ∈
        finiteGaloisConjugateIdeal g J :=
      Ideal.mem_map_of_mem _ hp
    rwa [hstable g] at hg

end

end TranslatedDepthSeven
