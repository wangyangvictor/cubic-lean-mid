import TranslatedDepthSeven.RankSevenNonvertexProjectionInternal
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-! Principal hypersurface ideals have no irrelevant-coordinate torsion
when there are at least two variables. Consequently a prime coordinate
saturation of an actual hypersurface section gives a prime principal ideal
after eliminating a monic linear equation. This connects the existing
projective Bertini output to literal restricted equations. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.IntegralHypersurfaceSectionElimination
open MvPolynomial TranslatedDepthSeven

variable {K σ : Type*} [Field K]

/-- Two distinct coordinate powers suffice to detect divisibility by an
arbitrary polynomial. No homogeneity or irreducibility is assumed. -/
theorem dvd_of_two_coordinate_powers
    (F G : MvPolynomial σ K) (i j : σ) (hij : i ≠ j) (a b : ℕ)
    (hi : F ∣ X i ^ a * G) (hj : F ∣ X j ^ b * G) : F ∣ G := by
  classical
  letI : GCDMonoid (MvPolynomial σ K) := UniqueFactorizationMonoid.toGCDMonoid _
  have hrel : IsRelPrime (X i : MvPolynomial σ K) (X j) :=
    (X_prime (R := K) (i := i)).irreducible.isRelPrime_iff_not_dvd.mpr
      (by simpa only [X_dvd_X] using hij)
  have hunit : IsUnit (gcd (X i ^ a : MvPolynomial σ K) (X j ^ b)) :=
    gcd_isUnit_iff_isRelPrime.mpr hrel.pow
  have h := (dvd_gcd hi hj).trans (gcd_mul_right' G (X i ^ a) (X j ^ b)).dvd
  exact hunit.dvd_mul_left.mp h

/-- Saturating a principal hypersurface ideal in every coordinate adds no
equations as soon as the polynomial ring has at least two variables. -/
theorem mem_span_of_coordinate_powers [Nontrivial σ]
    (F G : MvPolynomial σ K)
    (hsat : ∀ i : σ, ∃ a : ℕ,
      X i ^ a * G ∈ Ideal.span ({F} : Set (MvPolynomial σ K))) :
    G ∈ Ideal.span ({F} : Set (MvPolynomial σ K)) := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne σ
  obtain ⟨a, ha⟩ := hsat i
  obtain ⟨b, hb⟩ := hsat j
  exact Ideal.mem_span_singleton.mpr (dvd_of_two_coordinate_powers F G i j hij a b
    (Ideal.mem_span_singleton.mp ha) (Ideal.mem_span_singleton.mp hb))

/-- Literal elimination sends the hypersurface-plus-hyperplane ideal to
the principal ideal of the substituted polynomial. -/
theorem map_sectionIdeal (F : MvPolynomial (Option σ) K) (l : MvPolynomial σ K) :
    (Ideal.span ({F} : Set _) ⊔
      Ideal.span ({X none - rename some l} : Set _)).map
        (optionLinearEliminationAlgHom l).toRingHom =
      Ideal.span ({optionLinearEliminationAlgHom l F} : Set _) := by
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span]
  simp only [Set.image_singleton, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, optionLinearEliminationAlgHom_X_none,
    optionLinearEliminationAlgHom_rename_some, sub_self, Ideal.span_singleton_zero,
    sup_bot_eq]

/-- Elimination of a linear equation turns a prime all-coordinate
saturation of the section into primality of its actual defining equation.
The saturation hypothesis is exactly the one already constructed by the
projective Bertini theorem. -/
theorem eliminated_span_isPrime [Nontrivial σ]
    (F : MvPolynomial (Option σ) K) (l : MvPolynomial σ K)
    (J : Ideal (MvPolynomial (Option σ) K)) (hJ : J.IsPrime)
    (hle : Ideal.span ({F} : Set _) ⊔
      Ideal.span ({X none - rename some l} : Set _) ≤ J)
    (hsat : ∀ P ∈ J, ∀ i : Option σ, ∃ a : ℕ,
      X i ^ a * P ∈ Ideal.span ({F} : Set _) ⊔
        Ideal.span ({X none - rename some l} : Set _)) :
    (Ideal.span ({optionLinearEliminationAlgHom l F} : Set _)).IsPrime := by
  let φ := (optionLinearEliminationAlgHom l).toRingHom
  have hφ : Function.Surjective φ := optionLinearEliminationAlgHom_surjective l
  have hmap : J.map φ = Ideal.span ({optionLinearEliminationAlgHom l F} : Set _) := by
    apply le_antisymm
    · intro Q hQ
      obtain ⟨P, hP, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hQ
      apply mem_span_of_coordinate_powers
      intro i
      obtain ⟨a, ha⟩ := hsat P hP (some i)
      have hm := Ideal.mem_map_of_mem φ ha
      rw [map_sectionIdeal] at hm
      refine ⟨a, ?_⟩
      simpa only [φ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, map_pow, optionLinearEliminationAlgHom_X_some] using hm
    · rw [← map_sectionIdeal F l]
      exact Ideal.map_mono hle
  letI : J.IsPrime := hJ
  have hk : RingHom.ker φ ≤ J := by
    change RingHom.ker (optionLinearEliminationAlgHom l) ≤ J
    rw [ker_optionLinearEliminationAlgHom]
    exact le_trans le_sup_right hle
  have hp : (J.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hk
  rwa [hmap] at hp

/-- The literal affine coordinate ring, rather than only its projective
saturation, is a domain. -/
theorem eliminated_quotient_isDomain [Nontrivial σ]
    (F : MvPolynomial (Option σ) K) (l : MvPolynomial σ K)
    (J : Ideal (MvPolynomial (Option σ) K)) (hJ : J.IsPrime)
    (hle : Ideal.span ({F} : Set _) ⊔
      Ideal.span ({X none - rename some l} : Set _) ≤ J)
    (hsat : ∀ P ∈ J, ∀ i : Option σ, ∃ a : ℕ,
      X i ^ a * P ∈ Ideal.span ({F} : Set _) ⊔
        Ideal.span ({X none - rename some l} : Set _)) :
    IsDomain (MvPolynomial σ K ⧸
      Ideal.span ({optionLinearEliminationAlgHom l F} : Set _)) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr (eliminated_span_isPrime F l J hJ hle hsat)

end CubicTenVariables.IntegralHypersurfaceSectionElimination
