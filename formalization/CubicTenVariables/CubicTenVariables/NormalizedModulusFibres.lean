import CubicTenVariables.SquarefreePolynomialRoots
import Mathlib.Data.Fintype.BigOperators

/-! Actual lattice fibers with some coordinates fixed and the remaining
coordinates constrained by univariate polynomial relations. All coordinate
counts are derived here; none are supplied as input hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.NormalizedModulusFibres
open Polynomial SquarefreePolynomialRoots
open scoped BigOperators

/-- A finite vector set lies in the product of its actual coordinate images. -/
theorem card_le_prod_coordinate_images {n : ℕ} (S : Finset (Fin n → ℤ)) :
    S.card≤∏i,(S.image fun x => x i).card := by
  classical
  calc
    _ ≤ (Fintype.piFinset (fun i => S.image fun x => x i)).card :=
      Finset.card_le_card (fun x hx => Fintype.mem_piFinset.mpr
        (fun i => Finset.mem_image.mpr ⟨x,hx,rfl⟩))
    _ = _ := Fintype.card_piFinset _

theorem card_le_pow_of_coordinate_images {n : ℕ} (S : Finset (Fin n → ℤ)) (M : ℕ)
    (h : ∀i,(S.image fun x => x i).card≤M) : S.card≤M^n := by
  apply (card_le_prod_coordinate_images S).trans
  calc
    _ ≤ ∏_i : Fin n,M := Finset.prod_le_prod' (fun i _ => h i)
    _ = _ := by simp

theorem coordinate_image_le_one {n : ℕ} (S : Finset (Fin n → ℤ)) (i : Fin n) (z : ℤ)
    (h : ∀x∈S,x i=z) : (S.image fun x => x i).card≤1 := by
  classical
  apply (Finset.card_le_card (show (S.image fun x => x i)⊆{z} from ?_)).trans
    (by simp)
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_singleton.mpr (h x hx)

/-- Simultaneous squarefree roots and coprime progression, with a fixed set
of base coordinates. Polynomial coefficients may otherwise vary freely. -/
theorem card_le {n : ℕ} (S : Finset (Fin n → ℤ)) (J : Finset (Fin n))
    (z : Fin n → ℤ) (P : Fin n → Polynomial ℤ) (k : Fin n → ℕ) (D : ℕ) (C : ℤ)
    (hD : 1≤D) (hdeg : ∀i,i∉J → (P i).natDegree≤D)
    (hcoeff : ∀i,i∉J → (P i).coeff (k i)=C)
    (q m : ℕ) (hq : Squarefree q) [NeZero m] (hcop : q.Coprime m)
    (b : Fin n → ℤ) (u : Fin n → ℝ) (L : ℝ) (hL : 0≤L)
    (hsize : 1+L/(m : ℝ)≤(q : ℝ))
    (hfixed : ∀x∈S,∀i∈J,x i=z i)
    (hbox : ∀x∈S,∀i,|(x i : ℝ)-u i|≤L)
    (hres : ∀x∈S,∀i,(x i : ZMod m)=(b i : ZMod m))
    (hroot : ∀x∈S,∀i,i∉J → (P i).eval₂ (Int.castRingHom (ZMod q)) (x i : ZMod q)=0) :
    S.card≤(7*Nat.gcd C.natAbs q*D^q.primeFactors.card)^n := by
  apply card_le_pow_of_coordinate_images
  intro i
  by_cases hi : i∈J
  · apply (coordinate_image_le_one S i (z i) (fun x hx => hfixed x hx i hi)).trans
    have hg : 0<Nat.gcd C.natAbs q := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hq.ne_zero)
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · apply card_lifts_le (P i) D (k i) C hD (hdeg i hi) (hcoeff i hi)
      q m hq hcop (S.image fun x => x i) (b i) (u i) L hL hsize
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact hbox x hx i
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact hres x hx i
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact hroot x hx i hi

/-- Fixed nonzero leading (or other specified) coefficient: the numerical
constant is independent of all remaining coefficients and the base values. -/
theorem card_le_abs_coeff {n : ℕ} (S : Finset (Fin n → ℤ)) (J : Finset (Fin n))
    (z : Fin n → ℤ) (P : Fin n → Polynomial ℤ) (k : Fin n → ℕ) (D : ℕ) (C : ℤ)
    (hD : 1≤D) (hC : C≠0) (hdeg : ∀i,i∉J → (P i).natDegree≤D)
    (hcoeff : ∀i,i∉J → (P i).coeff (k i)=C)
    (q m : ℕ) (hq : Squarefree q) [NeZero m] (hcop : q.Coprime m)
    (b : Fin n → ℤ) (u : Fin n → ℝ) (L : ℝ) (hL : 0≤L)
    (hsize : 1+L/(m : ℝ)≤(q : ℝ))
    (hfixed : ∀x∈S,∀i∈J,x i=z i)
    (hbox : ∀x∈S,∀i,|(x i : ℝ)-u i|≤L)
    (hres : ∀x∈S,∀i,(x i : ZMod m)=(b i : ZMod m))
    (hroot : ∀x∈S,∀i,i∉J → (P i).eval₂ (Int.castRingHom (ZMod q)) (x i : ZMod q)=0) :
    S.card≤(7*C.natAbs*D^q.primeFactors.card)^n := by
  apply (card_le S J z P k D C hD hdeg hcoeff q m hq hcop b u L hL hsize
    hfixed hbox hres hroot).trans
  exact Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 7
    (Nat.le_of_dvd (Int.natAbs_pos.mpr hC) (Nat.gcd_dvd_left _ _)))) n

/-- Exact integral zeros need no modulus or box: each unfixed coordinate is
a root of a nonzero degree-bounded polynomial, so the vector count is at most
D^n. The common nonzero coefficient proves every required polynomial nonzero. -/
theorem card_exact_zeros_le {n : ℕ} (S : Finset (Fin n → ℤ)) (J : Finset (Fin n))
    (z : Fin n → ℤ) (P : Fin n → Polynomial ℤ) (k : Fin n → ℕ) (D : ℕ) (C : ℤ)
    (hD : 1≤D) (hC : C≠0) (hdeg : ∀i,i∉J → (P i).natDegree≤D)
    (hcoeff : ∀i,i∉J → (P i).coeff (k i)=C)
    (hfixed : ∀x∈S,∀i∈J,x i=z i)
    (hroot : ∀x∈S,∀i,i∉J → (P i).eval (x i)=0) : S.card≤D^n := by
  apply card_le_pow_of_coordinate_images
  intro i
  by_cases hi : i∈J
  · exact (coordinate_image_le_one S i (z i) (fun x hx => hfixed x hx i hi)).trans hD
  · have hP : P i≠0 := by
      intro hz
      have hc := hcoeff i hi
      rw [hz,Polynomial.coeff_zero] at hc
      exact hC hc.symm
    apply (Polynomial.card_le_degree_of_subset_roots (p := P i) ?_).trans (hdeg i hi)
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact (Polynomial.mem_roots hP).mpr (hroot x hx i hi)

end CubicTenVariables.NormalizedModulusFibres
