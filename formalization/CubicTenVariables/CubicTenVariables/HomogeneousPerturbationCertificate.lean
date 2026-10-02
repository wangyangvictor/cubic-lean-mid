import Mathlib.RingTheory.MvPolynomial.Homogeneous
import TranslatedDepthSeven.FractionFieldFiniteCoefficientClearing

/-!
# Fixed certificates for all lower-degree perturbations

The data here consist of actual linear forms and actual homogeneous polynomial
identities. A rational certificate descends to one principal localization of
the integers, chosen before any perturbation or residue characteristic.
-/

noncomputable section
namespace CubicTenVariables.HomogeneousPerturbationCertificate
open MvPolynomial TranslatedDepthSeven
open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S]
variable {n s : ℕ} {ι : Type*} [Fintype ι]

/-- Fixed leading-form identities after adjoining a linear projection. -/
structure Certificate (f : ι → MvPolynomial (Fin n) R)
    (e : ι → ℕ) (d : Fin n → ℕ) (s : ℕ) where
  forms : Fin s → MvPolynomial (Fin n) R
  forms_homogeneous : ∀ j, (forms j).IsHomogeneous 1
  powers_pos : ∀ i, 0 < d i
  coefficients : Fin n → (ι ⊕ Fin s) → MvPolynomial (Fin n) R
  coefficients_homogeneous : ∀ i j,
    (coefficients i j).IsHomogeneous (d i - Sum.elim e (fun _ => 1) j)
  coefficients_zero : ∀ i j, d i < Sum.elim e (fun _ => 1) j → coefficients i j = 0
  identity : ∀ i, (X i : MvPolynomial (Fin n) R) ^ d i =
    ∑ j, coefficients i j * Sum.elim f forms j

/-- Specialization preserves all the displayed certificates, even if some
leading equations become zero. -/
def Certificate.map {f : ι → MvPolynomial (Fin n) R} {e : ι → ℕ}
    {d : Fin n → ℕ} (D : Certificate f e d s) (φ : R →+* S) :
    Certificate (fun j => MvPolynomial.map φ (f j)) e d s where
  forms := fun j => MvPolynomial.map φ (D.forms j)
  forms_homogeneous := fun j => (D.forms_homogeneous j).map φ
  powers_pos := D.powers_pos
  coefficients := fun i j => MvPolynomial.map φ (D.coefficients i j)
  coefficients_homogeneous := fun i j => (D.coefficients_homogeneous i j).map φ
  coefficients_zero := fun i j h => by rw [D.coefficients_zero i j h, map_zero]
  identity := fun i => by
    have h := congrArg (MvPolynomial.map φ) (D.identity i)
    simp only [map_pow, map_X, map_sum, map_mul] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro j _
    cases j <;> rfl

/-- One denominator for a family with an arbitrary finite index type. -/
theorem exists_principal_model_family {α σ : Type*} [Fintype α]
    (f : α → MvPolynomial σ ℚ) :
    ∃ (Δ : ℤ) (hΔ : Δ ≠ 0),
      ∃ f₀ : α → MvPolynomial σ (Localization.Away Δ),
        ∀ i, MvPolynomial.map
          (awayToFractionRing (R := ℤ) (K := ℚ) Δ hΔ) (f₀ i) = f i := by
  let a := Fintype.equivFin α
  obtain ⟨Δ, hΔ, f₀, hf₀⟩ :=
    exists_common_principal_model_mvPolynomial_family (R := ℤ)
      (fun i => f (a.symm i))
  exact ⟨Δ, hΔ, fun i => f₀ (a i), fun i => by simpa using hf₀ (a i)⟩

/-- Descend all linear forms and coefficients simultaneously. The original
equations in the model are exactly the given integral equations. -/
theorem exists_principal_model (f : ι → MvPolynomial (Fin n) ℤ)
    (e : ι → ℕ) (d : Fin n → ℕ)
    (D : Certificate (fun j => MvPolynomial.map (Int.castRingHom ℚ) (f j)) e d s) :
    ∃ (Δ : ℤ) (_ : Δ ≠ 0), Nonempty
      (Certificate (fun j => MvPolynomial.map (Int.castRingHom (Localization.Away Δ))
        (f j)) e d s) := by
  classical
  let family : Fin s ⊕ (Fin n × (ι ⊕ Fin s)) → MvPolynomial (Fin n) ℚ :=
    Sum.elim D.forms (fun ij => D.coefficients ij.1 ij.2)
  obtain ⟨Δ, hΔ, family₀, hfamily₀⟩ := exists_principal_model_family family
  let φ := awayToFractionRing (R := ℤ) (K := ℚ) Δ hΔ
  have hφ : Function.Injective φ := awayToFractionRing_injective Δ hΔ
  let L : Fin s → MvPolynomial (Fin n) (Localization.Away Δ) :=
    fun j => family₀ (Sum.inl j)
  let c : Fin n → (ι ⊕ Fin s) → MvPolynomial (Fin n) (Localization.Away Δ) :=
    fun i j => family₀ (Sum.inr (i,j))
  have hL (j) : MvPolynomial.map φ (L j) = D.forms j := hfamily₀ (Sum.inl j)
  have hc (i j) : MvPolynomial.map φ (c i j) = D.coefficients i j :=
    hfamily₀ (Sum.inr (i,j))
  have hcomp : φ.comp (Int.castRingHom (Localization.Away Δ)) = Int.castRingHom ℚ :=
    RingHom.ext_int _ _
  refine ⟨Δ, hΔ, ⟨{
    forms := L
    forms_homogeneous := ?_
    powers_pos := D.powers_pos
    coefficients := c
    coefficients_homogeneous := ?_
    coefficients_zero := ?_
    identity := ?_ }⟩⟩
  · intro j
    apply IsHomogeneous.of_map hφ
    rw [hL]
    exact D.forms_homogeneous j
  · intro i j
    apply IsHomogeneous.of_map hφ
    rw [hc]
    exact D.coefficients_homogeneous i j
  · intro i j hij
    apply MvPolynomial.map_injective φ hφ
    rw [hc, D.coefficients_zero i j hij, map_zero]
  · intro i
    apply MvPolynomial.map_injective φ hφ
    simp only [map_pow, map_X, map_sum, map_mul, hc]
    rw [D.identity]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    cases j with
    | inl j => simp only [Sum.elim_inl, map_map, hcomp]
    | inr j => exact (hL j).symm

end CubicTenVariables.HomogeneousPerturbationCertificate
