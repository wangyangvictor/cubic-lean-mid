import TranslatedDepthSeven.BlockBivariatePolynomialDeterminant
import TranslatedDepthSeven.SurfaceNormalizationResidueDisc

/-! The integer determinant divisor obtained from all actual smooth residue
discs simultaneously. Different discs use their own formally etale chart.
The chart functions are represented by bivariate polynomials internally. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 1000000
universe u v w

/-- Entrywise congruence with the actual class-dependent polynomial
evaluations suffices; the modulus is the sum of the local jet exponents. -/
theorem blockBivariateIntegerEvaluations_det_dvd
    {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]
    (p : ℕ) (cls : ι → ν) (y : ν → Fin 2 → ℤ)
    (F : ν → ι → MvPolynomial (Fin 2) ℤ) (x : ι → Fin 2 → ℤ)
    (hx : ∀ j i, (p : ℤ) ∣ x j i - y (cls j) i)
    (A : Matrix ι ι ℤ)
    (hA : ∀ i j,
      (A i j : ZMod (p ^ (∑ c, smoothSurfaceJetExponent (Fintype.card {j // cls j = c})))) =
        (MvPolynomial.eval (x j) (F (cls j) i) : ℤ)) :
    (p : ℤ) ^ (∑ c, smoothSurfaceJetExponent (Fintype.card {j // cls j = c})) ∣
      A.det := by
  let E := ∑ c, smoothSurfaceJetExponent (Fintype.card {j // cls j = c})
  let B : Matrix ι ι ℤ := Matrix.of (fun i j => MvPolynomial.eval (x j) (F (cls j) i))
  have hB : (p : ℤ) ^ E ∣ B.det :=
    blockBivariatePolynomialEvaluation_det_dvd (p : ℤ) cls y F x hx
  have hmap : (Int.castRingHom (ZMod (p ^ E))).mapMatrix A =
      (Int.castRingHom (ZMod (p ^ E))).mapMatrix B := by
    ext i j
    exact hA i j
  change ((p ^ E : ℕ) : ℤ) ∣ A.det
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (Int.castRingHom (ZMod (p ^ E))) A.det = 0
  rw [(Int.castRingHom (ZMod (p ^ E))).map_det A, hmap,
    ← (Int.castRingHom (ZMod (p ^ E))).map_det B]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd B.det (p ^ E)).mpr hB

/-- One ambient polynomial has a single integral bivariate representative
valid for every point of the actual disc modulo the chosen prime power. -/
theorem SurfaceNormalizationResidueDisc.exists_bivariate_representatives
    {σ : Type u} {ι : Type v} {κ : Type*} {p E : ℕ} {hE : 0 < E}
    {y : ι → σ → ℤ}
    (disc : SurfaceNormalizationResidueDisc.{u,v,w} σ ι p E hE y)
    (F : κ → MvPolynomial σ ℤ) :
    ∃ G : κ → BivariateIntPolynomial, ∀ i j,
      (MvPolynomial.eval (y j) (F i) : ZMod (p ^ E)) =
        (MvPolynomial.eval (disc.parameters j) (G i) : ℤ) := by
  let G : κ → BivariateIntPolynomial := fun i =>
    bivariateEtaleDiscRepresentative p E hE disc.center disc.point disc.point_base
      (disc.ambient (F i))
  refine ⟨G, ?_⟩
  intro i j
  have hambient := RingHom.congr_fun (disc.specialization_ambient j) (F i)
  change disc.specialization j (disc.ambient (F i)) = _ at hambient
  have hrep := bivariateModularSpecialization_apply_eq_eval_representative
    p E hE (disc.parameters j) disc.center (disc.congruent j)
    disc.point disc.point_base (disc.specialization j)
    (disc.specialization_base j) (disc.specialization_reduction j) (disc.ambient (F i))
  rw [evalBivariateIntPolynomialZMod_eq_intCast_eval] at hrep
  have heval : (MvPolynomial.eval (y j) (F i) : ZMod (p ^ E)) =
      disc.specialization j (disc.ambient (F i)) := by
    rw [hambient]
    exact MvPolynomial.eval₂_comp (Int.castRingHom (ZMod (p ^ E))) (y j) (F i)
  exact heval.trans hrep

/-- Actual formal-etale discs on each fiber give the sum of their exponents,
even though the columns belong to different residue classes. -/
theorem surfaceResidueDiscBlocks_det_dvd
    {σ : Type u} {ι : Type v} {ν : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]
    (p : ℕ) (cls : ι → ν) (y : ι → σ → ℤ)
    (hE : 0 < ∑ c, smoothSurfaceJetExponent (Fintype.card {j // cls j = c}))
    (disc : ∀ c, SurfaceNormalizationResidueDisc.{u,v,w} σ {j // cls j = c} p
      (∑ c, smoothSurfaceJetExponent (Fintype.card {j // cls j = c})) hE
      (fun j => y j))
    (F : ι → MvPolynomial σ ℤ) :
    (p : ℤ) ^ (∑ c, smoothSurfaceJetExponent (Fintype.card {j // cls j = c})) ∣
      (Matrix.of (fun i j => MvPolynomial.eval (y j) (F i))).det := by
  classical
  choose G hG using fun c => (disc c).exists_bivariate_representatives F
  apply blockBivariateIntegerEvaluations_det_dvd p cls (fun c => (disc c).center)
    G (fun j => (disc (cls j)).parameters ⟨j, rfl⟩)
  · intro j i
    exact (disc (cls j)).congruent ⟨j, rfl⟩ i
  · intro i j
    exact hG (cls j) i ⟨j, rfl⟩

end
end TranslatedDepthSeven
