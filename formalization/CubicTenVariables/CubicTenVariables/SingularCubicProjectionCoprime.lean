import CubicTenVariables.SingularCubicLinearFibers
import CubicTenVariables.Literature.FiniteFieldPointCounts
import TranslatedDepthSeven.AffinePolynomialChange
import TranslatedDepthSeven.QbarPrimeAlgebraicCoefficientExtension
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Coprimality of the actual quadratic and cubic equations obtained by
projecting an integral cubic from a singular point.  The proof uses an exact
polynomial substitution, including over finite fields.  The nonzero quadratic
section remains an explicit hypothesis; it is not deduced from integrality.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.SingularCubicProjectionCoprime
open MvPolynomial HessianTheorem11 CubicTaylorExpansion CubicSingularQuotient
open SingularCubicLinearFibers TranslatedDepthSeven
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

/-- Pull chart polynomials back along projection parallel to z. -/
def pullback (z : Fin (n+1) → K) (i : Fin (n+1)) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n+1)) K :=
  aeval (fun j => X (i.succAbove j)-C (z (i.succAbove j)/z i)*X i)

/-- The coordinate hyperplane is a polynomial retraction of the projection. -/
theorem section_pullback (z : Fin (n+1) → K) (i : Fin (n+1))
    (G : MvPolynomial (Fin n) K) :
    zeroSection i (pullback z i G)=G := by
  have he : (aeval (i.insertNth 0 (X : Fin n → MvPolynomial (Fin n) K))).comp
      (pullback z i) = AlgHom.id K (MvPolynomial (Fin n) K) := by
    ext j
    simp [pullback]
  exact AlgHom.congr_fun he G

theorem pullback_section (z : Fin (n+1) → K) (i : Fin (n+1))
    (G : MvPolynomial (Fin (n+1)) K) :
    pullback z i (zeroSection i G)=
      eval₂ C (i.insertNth 0
        (fun j => X (i.succAbove j)-C (z (i.succAbove j)/z i)*X i)) G := by
  unfold pullback zeroSection
  rw [comp_aeval_apply]
  have he : (fun k => aeval
      (fun j => X (i.succAbove j)-C (z (i.succAbove j)/z i)*X i)
      (@Fin.insertNth n (fun _ => MvPolynomial (Fin n) K) i 0 X k)) =
      i.insertNth 0
        (fun j => X (i.succAbove j)-C (z (i.succAbove j)/z i)*X i) := by
    funext j
    induction j using i.succAboveCases <;> simp
  rw [he]
  rfl

/-- An identity of polynomials, not only of their finite-field evaluations. -/
theorem polynomial_identity
    (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous 3)
    (z : Fin (n+1) → K) (hzero : eval z F=0) (hsing : gradient F z=0)
    (i : Fin (n+1)) (hi : z i ≠ 0) :
    F = (C ((z i)⁻¹)*X i)*pullback z i (zeroSection i (quadraticPolynomial F z))+
      pullback z i (zeroSection i F) := by
  let u : Fin (n+1) → MvPolynomial (Fin (n+1)) K :=
    i.insertNth 0 (fun j => X (i.succAbove j)-C (z (i.succAbove j)/z i)*X i)
  let w : Fin (n+1) → MvPolynomial (Fin (n+1)) K := fun j => C (z j)
  let t : MvPolynomial (Fin (n+1)) K := C ((z i)⁻¹)*X i
  have hrecover : u+t • w=X := by
    funext j
    induction j using i.succAboveCases
    · simp only [u,w,t,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Fin.insertNth_apply_same]
      rw [zero_add,mul_right_comm,← map_mul,inv_mul_cancel₀ hi,map_one,one_mul]
    · simp only [u,w,t,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
        Fin.insertNth_apply_succAbove,div_eq_mul_inv,map_mul]
      ring
  have hconst (G : MvPolynomial (Fin (n+1)) K) :
      eval₂ C w G=(C (eval z G) : MvPolynomial (Fin (n+1)) K) := by
    simpa only [RingHom.comp_id] using
      (eval₂_comp_left C (RingHom.id K) z G).symm
  have hgrad (j : Fin (n+1)) : eval z (pderiv j F)=0 := congrFun hsing j
  have hquad : dotProduct u (fun j => eval₂ C w (pderiv j F))=0 := by
    simp only [dotProduct,hconst,hgrad,map_zero,mul_zero,Finset.sum_const_zero]
  have hlin : dotProduct w (fun j => eval₂ C u (pderiv j F))=
      eval₂ C u (quadraticPolynomial F z) := by
    simp only [quadraticPolynomial,eval₂_sum,eval₂_mul,eval₂_C,dotProduct,w]
  have he := eval₂_cubic_add_smul F hF C u w t
  rw [hrecover,eval₂_eta,hquad,hlin,hconst,hzero,map_zero,mul_zero,mul_zero,
    add_zero,add_zero] at he
  rw [pullback_section,pullback_section]
  simpa only [u,t,add_comm] using he

theorem pullback_totalDegree_le (z : Fin (n+1) → K) (i : Fin (n+1))
    (G : MvPolynomial (Fin n) K) :
    (pullback z i G).totalDegree ≤ G.totalDegree := by
  apply totalDegree_aeval_le_of_totalDegree_le_one
  intro j
  exact (totalDegree_sub _ _).trans (max_le (by simp) (by
    simpa using (isHomogeneous_C_mul_X (z (i.succAbove j)/z i) i).totalDegree_le))

/-- Base-field irreducibility already suffices for the actual common-divisor
argument.  A common divisor has degree at most two and lifts to a divisor of F. -/
theorem of_irreducible
    (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (z : Fin (n+1) → K) (hzero : eval z F=0) (hsing : gradient F z=0)
    (i : Fin (n+1)) (hi : z i ≠ 0)
    (hQ : zeroSection i (quadraticPolynomial F z) ≠ 0) :
    IsRelPrime (zeroSection i (quadraticPolynomial F z)) (zeroSection i F) := by
  intro G hGQ hGC
  have hG : G ≠ 0 := ne_zero_of_dvd_ne_zero hQ hGQ
  have hPG : pullback z i G ≠ 0 := by
    intro he
    have h := congrArg (zeroSection i) he
    rw [section_pullback] at h
    exact hG (by simpa [zeroSection] using h)
  have hdiv : pullback z i G ∣ F := by
    rw [polynomial_identity F hF z hzero hsing i hi]
    exact dvd_add (dvd_mul_of_dvd_right (map_dvd (pullback z i) hGQ) _)
      (map_dvd (pullback z i) hGC)
  obtain ⟨H,hH⟩ := hdiv
  rcases hirr.isUnit_or_isUnit hH with hunit | hunit
  · have h := hunit.map (aeval (i.insertNth 0 (X : Fin n → MvPolynomial (Fin n) K)))
    exact (section_pullback z i G) ▸ h
  · rcases hunit with ⟨v,rfl⟩
    have hback : F ∣ pullback z i G := ⟨(v⁻¹ : (MvPolynomial (Fin (n+1)) K)ˣ),by
      rw [hH]
      simp only [mul_assoc,Units.mul_inv,mul_one]⟩
    have hlow : (pullback z i G).totalDegree ≤ 2 :=
      (pullback_totalDegree_le z i G).trans
        ((totalDegree_le_of_dvd_of_isDomain hGQ hQ).trans
          (homogeneous_section i _ (homogeneous_quadraticPolynomial F hF z)).totalDegree_le)
    have hhigh := totalDegree_le_of_dvd_of_isDomain hback hPG
    rw [hF.totalDegree hirr.ne_zero] at hhigh
    omega

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Geometric integrality implies the base-field primality needed above;
faithfully flat coefficient extension reflects the actual principal ideal. -/
theorem irreducible_of_geometricallyIntegral
    (F : MvPolynomial (Fin (n+1)) K) (hI : Literature.GeometricallyIntegralForm F) :
    Irreducible F := by
  let L := AlgebraicClosure K
  let R := MvPolynomial (Fin (n+1)) K
  let S := MvPolynomial (Fin (n+1)) L
  let I : Ideal R := Ideal.span {F}
  let φ : R →+* S := map (algebraMap K L)
  letI : Module.FaithfullyFlat R S := mvPolynomial_faithfullyFlat
  have hmap : I.map φ = Ideal.span {map (algebraMap K L) F} := by
    simp only [I,φ,Ideal.map_span,Set.image_singleton]
    rfl
  have hp : (I.map φ).IsPrime := by
    rw [hmap]
    exact (Ideal.Quotient.isDomain_iff_prime _).mp hI.2
  letI := hp
  have hc : (I.map φ).comap φ=I := Ideal.comap_map_eq_self_of_faithfullyFlat I
  have hIp : I.IsPrime := hc ▸ (Ideal.comap_isPrime φ (I.map φ))
  exact ((Ideal.span_singleton_prime hI.1).mp hIp).irreducible

/-- Literal geometric-integrality form for the singular-point chart used
in the finite-field projection count. -/
theorem of_geometricallyIntegral
    (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous 3)
    (hI : Literature.GeometricallyIntegralForm F)
    (z : Fin (n+1) → K) (hzero : eval z F=0) (hsing : gradient F z=0)
    (i : Fin (n+1)) (hi : z i ≠ 0)
    (hQ : zeroSection i (quadraticPolynomial F z) ≠ 0) :
    IsRelPrime (zeroSection i (quadraticPolynomial F z)) (zeroSection i F) :=
  of_irreducible F hF (irreducible_of_geometricallyIntegral F hI) z hzero hsing i hi hQ

end CubicTenVariables.SingularCubicProjectionCoprime
