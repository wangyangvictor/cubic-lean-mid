import TranslatedDepthSeven.GaloisConjugateIntersection
import TranslatedDepthSeven.HomogeneousMinimalComponents
import TranslatedDepthSeven.FiniteComponentFrontier
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Galois conjugates of geometric minimal components

The results here isolate the elementary, non-descent branch of the Galois
rationality argument.  A rational point on a component belongs to every
coefficientwise conjugate component.  Thus, when one conjugate is distinct,
the point belongs to the frontier cut out by the sum of the two component
ideals, whose minimal components have strictly smaller Krull dimension.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v

variable {K : Type u} {σ : Type v} [Field K] [Algebra ℚ K]

/-- Coefficientwise conjugation of an ideal. -/
def conjugateIdeal (g : K ≃ₐ[ℚ] K) (P : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial σ K) :=
  P.map (conjugatePolynomial g).toRingHom

/-- Coefficient extension of an ideal defined over `ℚ` is invariant under
every `ℚ`-automorphism of the coefficient field. -/
theorem conjugateIdeal_map_rationalCoefficientIdeal
    (g : K ≃ₐ[ℚ] K) (J : Ideal (MvPolynomial σ ℚ)) :
    conjugateIdeal g
        (J.map (MvPolynomial.map (algebraMap ℚ K))) =
      J.map (MvPolynomial.map (algebraMap ℚ K)) := by
  rw [conjugateIdeal, Ideal.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro q
    simp [RingHom.comp_apply, conjugatePolynomial_apply]
  · intro i
    simp [RingHom.comp_apply, conjugatePolynomial_apply]

/-- An ideal is either invariant under every coefficient automorphism or
has a distinct coefficientwise conjugate. -/
theorem conjugateIdeal_fixed_or_exists_distinct
    (P : Ideal (MvPolynomial σ K)) :
    (∀ g : K ≃ₐ[ℚ] K, conjugateIdeal g P = P) ∨
      ∃ g : K ≃ₐ[ℚ] K, conjugateIdeal g P ≠ P := by
  classical
  by_cases h : ∀ g : K ≃ₐ[ℚ] K, conjugateIdeal g P = P
  · exact Or.inl h
  · exact Or.inr (not_forall.mp h)

/-- A polynomial over an algebraic closure of `ℚ` fixed coefficientwise by
every `ℚ`-automorphism has rational coefficients. -/
theorem exists_rationalPolynomial_of_fixed_by_all
    (f : MvPolynomial σ (AlgebraicClosure ℚ))
    (hfixed : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      conjugatePolynomial g f = f) :
    ∃ f₀ : MvPolynomial σ ℚ,
      MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)) f₀ = f := by
  change f ∈ Set.range
    (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
  intro c hc
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro g
  change c ∈ f.coeffs at hc
  rw [MvPolynomial.mem_coeffs_iff] at hc
  obtain ⟨d, -, hd⟩ := hc
  have heq := congrArg (MvPolynomial.coeff d) (hfixed g)
  rw [conjugatePolynomial_apply, MvPolynomial.coeff_map] at heq
  rw [hd]
  exact heq

/-- Elementwise Galois-fixed ideals descend by contraction.  This is the
final elementary step once semilinear subspace descent has upgraded setwise
invariance of each finite-dimensional homogeneous piece to elementwise
fixed rational generators. -/
theorem ideal_eq_map_comap_of_every_element_fixed
    (P : Ideal (MvPolynomial σ (AlgebraicClosure ℚ)))
    (hfixed : ∀ f ∈ P,
      ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        conjugatePolynomial g f = f) :
    (P.comap (MvPolynomial.map
      (algebraMap ℚ (AlgebraicClosure ℚ)))).map
        (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))) = P := by
  apply le_antisymm
  · exact (Ideal.map_le_iff_le_comap).mpr le_rfl
  · intro f hf
    obtain ⟨f₀, hf₀⟩ :=
      exists_rationalPolynomial_of_fixed_by_all f (hfixed f hf)
    rw [← hf₀]
    exact Ideal.mem_map_of_mem _ (show f₀ ∈ P.comap
      (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))) by
        change MvPolynomial.map
          (algebraMap ℚ (AlgebraicClosure ℚ)) f₀ ∈ P
        rwa [hf₀])

/-- A rational affine point annihilating an ideal also annihilates its
coefficientwise conjugate. -/
theorem conjugateIdeal_le_rationalEvaluationKernel
    (g : K ≃ₐ[ℚ] K) (P : Ideal (MvPolynomial σ K)) (x : σ → ℚ)
    (hx : P ≤ RingHom.ker (MvPolynomial.eval
      (fun i ↦ algebraMap ℚ K (x i)))) :
    conjugateIdeal g P ≤ RingHom.ker (MvPolynomial.eval
      (fun i ↦ algebraMap ℚ K (x i))) := by
  rw [conjugateIdeal, Ideal.map_le_iff_le_comap]
  intro f hf
  change MvPolynomial.eval (fun i ↦ algebraMap ℚ K (x i))
      (conjugatePolynomial g f) = 0
  rw [← conjugatePoint_algebraMap g x,
    eval_conjugatePolynomial, show MvPolynomial.eval
      (fun i ↦ algebraMap ℚ K (x i)) f = 0 from hx hf, map_zero]

/-- A ring equivalence carries a minimal prime over `I` to a minimal prime
over the transported ideal. -/
theorem map_mem_minimalPrimes_of_ringEquiv
    {R : Type u} [CommRing R] (e : R ≃+* R) {I P : Ideal R}
    (hP : P ∈ I.minimalPrimes) :
    P.map e ∈ (I.map e).minimalPrimes := by
  letI : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  letI : (P.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  refine ⟨⟨inferInstance, Ideal.map_mono hP.1.2⟩, ?_⟩
  intro Q hQ hQP
  have hcomPrime : (Q.comap e).IsPrime := hQ.1.comap e
  have hIcom : I ≤ Q.comap e :=
    (Ideal.map_le_iff_le_comap).mp hQ.2
  have hcomP : Q.comap e ≤ P := by
    intro f hf
    have hef : e f ∈ P.map e := hQP hf
    exact (Ideal.apply_mem_of_equiv_iff).mp hef
  have hPcom : P ≤ Q.comap e := hP.2 ⟨hcomPrime, hIcom⟩ hcomP
  exact (Ideal.map_le_iff_le_comap).mpr hPcom

/-- Invariance of the defining ideal implies that a conjugate of any minimal
component is again a minimal component of the same ideal. -/
theorem conjugateIdeal_mem_minimalPrimes_of_invariant
    {I P : Ideal (MvPolynomial σ K)}
    (hP : P ∈ I.minimalPrimes) (g : K ≃ₐ[ℚ] K)
    (hI : conjugateIdeal g I = I) :
    conjugateIdeal g P ∈ I.minimalPrimes := by
  rw [← hI]
  exact map_mem_minimalPrimes_of_ringEquiv
    (conjugatePolynomial g) hP

variable [IsNoetherianRing (MvPolynomial σ K)]

/-- The complete distinct-conjugate branch.  If `P` and its conjugate are
minimal components of the same rationally defined ideal, then every rational
point of `P` belongs to a minimal component of their frontier.  That frontier
component strictly contains both ideals and has smaller finite quotient
Krull dimension. -/
theorem exists_lowerDimensional_conjugateFrontier_through_rationalPoint
    {I P : Ideal (MvPolynomial σ K)} {s : ℕ}
    (hP : P ∈ finiteMinimalPrimes I)
    (g : K ≃ₐ[ℚ] K)
    (hI : conjugateIdeal g I = I)
    (hne : conjugateIdeal g P ≠ P)
    (hPdim : ringKrullDim (MvPolynomial σ K ⧸ P) = s)
    (x : σ → ℚ)
    (hx : P ≤ RingHom.ker (MvPolynomial.eval
      (fun i ↦ algebraMap ℚ K (x i)))) :
    ∃ L ∈ finiteMinimalPrimes (P ⊔ conjugateIdeal g P),
      P < L ∧ conjugateIdeal g P < L ∧
      L ≤ RingHom.ker (MvPolynomial.eval
        (fun i ↦ algebraMap ℚ K (x i))) ∧
      ringKrullDim (MvPolynomial σ K ⧸ L) < s := by
  let T : Ideal (MvPolynomial σ K) :=
    RingHom.ker (MvPolynomial.eval (fun i ↦ algebraMap ℚ K (x i)))
  letI : T.IsPrime := RingHom.ker_isPrime _
  have hgT : conjugateIdeal g P ≤ T :=
    conjugateIdeal_le_rationalEvaluationKernel g P x hx
  have hconj : conjugateIdeal g P ∈ finiteMinimalPrimes I := by
    rw [mem_finiteMinimalPrimes_iff]
    exact conjugateIdeal_mem_minimalPrimes_of_invariant
      ((mem_finiteMinimalPrimes_iff I P).mp hP) g hI
  obtain ⟨L, hL, hPL, hgL, hLT⟩ :=
    exists_strict_frontierMinimalPrime_le hP hconj hne.symm hx hgT
  exact ⟨L, hL, hPL, hgL, hLT,
    ringKrullDim_frontier_lt_nat_of_distinct_finiteMinimalPrimes
      hP hconj hne.symm hL hPdim⟩

/-- Galois rationality dichotomy for a minimal component of the coefficient
extension of a rational ideal.  The non-invariant alternative includes the
literal lower-dimensional frontier containing the given rational point. -/
theorem rationalMinimalComponent_fixed_or_lowerDimensionalFrontier
    (J : Ideal (MvPolynomial σ ℚ))
    {P : Ideal (MvPolynomial σ K)} {s : ℕ}
    (hP : P ∈ finiteMinimalPrimes
      (J.map (MvPolynomial.map (algebraMap ℚ K))))
    (hPdim : ringKrullDim (MvPolynomial σ K ⧸ P) = s)
    (x : σ → ℚ)
    (hx : P ≤ RingHom.ker (MvPolynomial.eval
      (fun i ↦ algebraMap ℚ K (x i)))) :
    (∀ g : K ≃ₐ[ℚ] K, conjugateIdeal g P = P) ∨
      ∃ g : K ≃ₐ[ℚ] K,
        ∃ L ∈ finiteMinimalPrimes (P ⊔ conjugateIdeal g P),
          P < L ∧ conjugateIdeal g P < L ∧
          L ≤ RingHom.ker (MvPolynomial.eval
            (fun i ↦ algebraMap ℚ K (x i))) ∧
          ringKrullDim (MvPolynomial σ K ⧸ L) < s := by
  rcases conjugateIdeal_fixed_or_exists_distinct P with hfixed | ⟨g, hg⟩
  · exact Or.inl hfixed
  · exact Or.inr ⟨g,
      exists_lowerDimensional_conjugateFrontier_through_rationalPoint
        hP g (conjugateIdeal_map_rationalCoefficientIdeal g J)
        hg hPdim x hx⟩

end

end TranslatedDepthSeven
