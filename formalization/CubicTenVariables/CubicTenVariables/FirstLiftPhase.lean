import CubicTenVariables.CubicTaylorExpansion
import CubicTenVariables.LiftingCharacters

/-! Taylor congruences and exact exponential phases for the square-full
first lift, in the original integer representative convention. -/

noncomputable section
namespace CubicTenVariables.FirstLiftPhase
open MvPolynomial HessianTheorem11 CubicTaylorExpansion LiftingCharacters

def integerPhase {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (a : ℤ) (x v : Fin n → ℤ) : ℤ :=
  a * eval x F + dotProduct v x

/-- The remainder has an actual integral factor m², so no factorial
division or residue-characteristic restriction enters the congruence. -/
theorem sq_dvd_phase_difference {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (y h v : Fin n → ℤ) (a e m : ℤ) :
    m^2 ∣ integerPhase F (a+m*e) (y+m•h) v -
      (integerPhase F a y v + m*(e*eval y F + dotProduct (a•gradient F y+v) h)) := by
  refine ⟨a * quadraticAt F y h + a*m*eval h F + e*directional F y h +
    m*e*quadraticAt F y h + m^2*e*eval h F, ?_⟩
  unfold integerPhase
  rw [eval_cubic_add_smul F hF]
  simp only [dotProduct_add, dotProduct_smul, add_dotProduct, smul_dotProduct,
    smul_eq_mul]
  rw [show dotProduct (gradient F y) h = directional F y h from dotProduct_comm _ _]
  ring

/-- The literal exponential factors into its low-digit phase and the
linear character in the high digits. A∣M suffices. -/
theorem residueExponential_firstLift {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A M : ℕ) [NeZero A] [NeZero M]
    (hAM : A ∣ M) (y h v : Fin n → ℤ) (a e : ℤ) :
    residueExponential (A*M) (integerPhase F (a+(M:ℤ)*e) (y+(M:ℤ)•h) v) =
      residueExponential (A*M) (integerPhase F a y v) *
        residueExponential A (e*eval y F + dotProduct (a•gradient F y+v) h) := by
  have hq : ((A*M : ℕ) : ℤ) ∣ (M : ℤ)^2 := by
    obtain ⟨k, rfl⟩ := hAM
    refine ⟨(k : ℤ), ?_⟩
    push_cast
    ring
  have hd := hq.trans (sq_dvd_phase_difference F hF y h v a e (M:ℤ))
  have hc :
      (integerPhase F (a+(M:ℤ)*e) (y+(M:ℤ)•h) v : ZMod (A*M)) =
      ((integerPhase F a y v +
        (M:ℤ)*(e*eval y F + dotProduct (a•gradient F y+v) h) : ℤ) : ZMod (A*M)) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
    simpa only [neg_sub] using (dvd_neg.mpr hd)
  rw [residueExponential_eq_of_cast_eq (A*M) hc, residueExponential_add,
    residueExponential_mul_modulus]

end CubicTenVariables.FirstLiftPhase
