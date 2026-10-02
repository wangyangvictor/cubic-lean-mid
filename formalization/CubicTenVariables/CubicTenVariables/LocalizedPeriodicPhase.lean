import CubicTenVariables.LocalizedSums
import CubicTenVariables.PrimeSumAdapter
import CubicTenVariables.DeltaMethod

/-! The actual periodic coefficient in the localized generating function.
Polynomial evaluation, integer representatives and the two residue moduli
are retained explicitly. No Poisson or counting estimate is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.LocalizedPeriodicPhase
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def coefficient (G : MvPolynomial (Fin n) ℤ) (q W : ℕ)
    (Ω : Set (Fin n → ZMod W)) (x : Fin n → ℤ) : ℂ :=
  ∑ a : Fin q, if Nat.Coprime a.val q then
    if integerResidue W x ∈ Ω then residueExponential q ((a.val:ℤ)*eval x G) else 0
  else 0

theorem cast_eval_eq (G : MvPolynomial (Fin n) ℤ) (q : ℕ)
    (x y : Fin n → ℤ) (hxy : ∀ i, (x i : ZMod q)=(y i : ZMod q)) :
    (eval x G : ZMod q)=(eval y G : ZMod q) := by
  have hx := MvPolynomial.map_eval (Int.castRingHom (ZMod q)) x G
  have hy := MvPolynomial.map_eval (Int.castRingHom (ZMod q)) y G
  simp only [Function.comp_def,Int.coe_castRingHom] at hx hy
  rw [hx,hy]
  rw [show (fun i => (x i:ZMod q))=(fun i => (y i:ZMod q)) from funext hxy]

theorem coefficient_eq_of_residues (G : MvPolynomial (Fin n) ℤ) (q W : ℕ)
    (hq : 0 < q) (Ω : Set (Fin n → ZMod W)) (x y : Fin n → ℤ)
    (hqxy : ∀ i, (x i : ZMod q)=(y i : ZMod q))
    (hWxy : integerResidue W x=integerResidue W y) :
    coefficient G q W Ω x=coefficient G q W Ω y := by
  letI : NeZero q := ⟨hq.ne'⟩
  unfold coefficient
  apply Finset.sum_congr rfl
  intro a _
  rw [hWxy]
  split_ifs <;> try rfl
  rw [PrimeSumAdapter.residueExponential_eq_stdAddChar,
    PrimeSumAdapter.residueExponential_eq_stdAddChar]
  congr 1
  simp only [Int.cast_mul,Int.cast_natCast,cast_eval_eq G q x y hqxy]

/-- Any common multiple of both moduli is an actual coefficient period. -/
theorem coefficient_lattice_translate (G : MvPolynomial (Fin n) ℤ)
    (q W d : ℕ) (hq : 0 < q) (hqd : q ∣ d) (hWd : W ∣ d)
    (Ω : Set (Fin n → ZMod W)) (x z : Fin n → ℤ) :
    coefficient G q W Ω (fun i => x i+(d:ℤ)*z i)=coefficient G q W Ω x := by
  have hq0 : (d:ZMod q)=0 := (ZMod.natCast_eq_zero_iff d q).mpr hqd
  have hW0 : (d:ZMod W)=0 := (ZMod.natCast_eq_zero_iff d W).mpr hWd
  apply coefficient_eq_of_residues G q W hq Ω _ x
  · intro i
    simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,hq0,zero_mul,add_zero]
  · funext i
    simp only [integerResidue,Int.cast_add,Int.cast_mul,Int.cast_natCast,hW0,zero_mul,add_zero]

/-- The finite Fourier coefficient is precisely the localized complete sum. -/
theorem finite_fourier_eq (G : MvPolynomial (Fin n) ℤ) (q W : ℕ)
    (Ω : Set (Fin n → ZMod W)) (v : Fin n → ℤ) :
    (∑ x : Fin n → Fin (Nat.lcm q W),
      coefficient G q W Ω (fun i => ((x i).val:ℤ))*
        residueExponential (Nat.lcm q W) (∑ i, v i*(x i).val)) =
      localizedCompleteCubicSum G q W Ω v := by
  unfold coefficient localizedCompleteCubicSum
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs with ha
  · apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  · simp

end CubicTenVariables.LocalizedPeriodicPhase
