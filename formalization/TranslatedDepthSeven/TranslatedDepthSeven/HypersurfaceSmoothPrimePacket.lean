import TranslatedDepthSeven.HypersurfaceSmoothPrimeReservoir
import TranslatedDepthSeven.ProgressionNormalizationBlockEvaluation

/-! Usable squarefree moduli from the prime reservoir feed actual
progression residue packets. Congruence is in displacement coordinates,
while nonsingularity is evaluated in the original affine coordinates. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
universe u

/-- Every packet modulo the selected modulus has the local hypotheses used
by the progression auxiliary-form theorem, using its actual base point. -/
theorem hypersurfaceProgression_packet_inputs_of_usable_modulus
    {ι : Type u} (F : MvPolynomial (Fin 4) ℤ) (u z : Fin 3 → ℤ)
    (y : ι → Fin 3 → ℤ) (m q : ℕ) (hqm : Nat.Coprime q m)
    (hyq : ∀ j i, (q : ℤ) ∣ y j i - z i)
    (hgood : ∀ p, p.Prime → p ∣ q → ∃ v,
      (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
        (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    ∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
      ∃ (z' : Fin 3 → ℤ) (v : Fin 3),
        (∀ j i, (p : ℤ) ∣ y j i - z' i) ∧
        (MvPolynomial.eval (fun i => u i + (m : ℤ) * z' i)
          (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0 := by
  intro p hp hpq
  obtain ⟨v, hv⟩ := hgood p hp hpq
  refine ⟨hp.coprime_iff_not_dvd.mp (hqm.of_dvd_left hpq), z, v, ?_, hv⟩
  intro j i
  have hpqZ : (p : ℤ) ∣ (q : ℤ) := by exact_mod_cast hpq
  exact hpqZ.trans (hyq j i)

/-- The chosen prime modulus supplies actual formally-etale residue discs
for any nonempty packet of equation zeros in its congruence class. No chart,
specialization map, or determinant assertion is an input. -/
theorem hypersurfaceProgression_residueDiscs_of_usable_modulus
    {ι : Type u} [Nonempty ι]
    (F : MvPolynomial (Fin 4) ℤ) (u z : Fin 3 → ℤ)
    (y : ι → Fin 3 → ℤ) (m q E : ℕ) (hE : 0 < E)
    (hqm : Nat.Coprime q m)
    (hyF : ∀ j, MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) F = 0)
    (hyq : ∀ j i, (q : ℤ) ∣ y j i - z i)
    (hgood : ∀ p, p.Prime → p ∣ q → ∃ v,
      (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
        (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    ∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
      Nonempty (SurfaceNormalizationResidueDisc.{0,u,0} (Fin 4) ι p E hE
        (fun j => progressionHomogeneousPoint u m (y j))) := by
  intro p hp hpq
  obtain ⟨hpm, z', v, hyz', hz'⟩ :=
    hypersurfaceProgression_packet_inputs_of_usable_modulus F u z y m q hqm hyq hgood p hp hpq
  refine ⟨hpm, ⟨surfaceHypersurfaceFirstChartResidueDiscAt p E hp hE F
    (fun j i => u i + (m : ℤ) * y j i) (fun i => u i + (m : ℤ) * z' i)
    hyF ?_ v hz'⟩⟩
  intro j i
  convert dvd_mul_of_dvd_right (hyz' j i) (m : ℤ) using 1 <;> ring

end
end TranslatedDepthSeven
