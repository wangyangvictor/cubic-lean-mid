import TranslatedDepthSeven.AllResidueSurfaceDeterminant
import TranslatedDepthSeven.HypersurfaceSurfaceResidueDiscCoordinates

/-! The all-residue divisor for a literal integral affine hypersurface in
three variables. The charts and their common bivariate representatives are
constructed from the actual nonzero partial derivatives. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Classes with displayed integral centers. Nonempty fibers and a nonzero
partial at each center construct the formal-etale charts internally. -/
theorem hypersurfaceResidueClasses_det_dvd
    {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]
    (p : ℕ) (hp : p.Prime) (cls : ι → ν)
    (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ) (z : ν → Fin 3 → ℤ)
    (hne : ∀ c, Nonempty {j // cls j = c})
    (hF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (hcong : ∀ j i, (p : ℤ) ∣ y j i - z (cls j) i)
    (hgrad : ∀ c, ∃ v, (MvPolynomial.eval (z c) (MvPolynomial.pderiv v F) : ZMod p) ≠ 0)
    (G : ι → MvPolynomial (Fin 3) ℤ) :
    (p : ℤ) ^ (∑ c, smoothSurfaceJetExponent (Fintype.card {j // cls j = c})) ∣
      (Matrix.of (fun i j => MvPolynomial.eval (y j) (G i))).det := by
  classical
  by_cases hE : 0 < ∑ c, smoothSurfaceJetExponent (Fintype.card {j // cls j = c})
  · apply surfaceResidueDiscBlocks_det_dvd p cls y hE _ G
    intro c
    letI : Nonempty {j // cls j = c} := hne c
    let v := (hgrad c).choose
    have hv := (hgrad c).choose_spec
    exact surfaceHypersurfaceResidueDiscAt (ι := {j // cls j = c})
      p _ hp hE F (fun j => y j) (z c)
      (fun j => hF j) (fun j i => by simpa only [j.property] using hcong j i) v hv
  · have hz : (∑ c, smoothSurfaceJetExponent (Fintype.card {j // cls j = c})) = 0 :=
      Nat.eq_zero_of_not_pos hE
    simp only [hz, pow_zero, one_dvd]

/-- Coordinatewise reduction of an integral point. -/
def integralSurfaceResidue (p : ℕ) (x : Fin 3 → ℤ) : Fin 3 → ZMod p :=
  fun i => (x i : ZMod p)

/-- Only occupied classes, obtained from the displayed points themselves. -/
abbrev SurfaceOccupiedResidueClass {ι : Type*} (p : ℕ) (y : ι → Fin 3 → ℤ) :=
  Set.range (fun j => integralSurfaceResidue p (y j))

def surfacePointResidueClass {ι : Type*} (p : ℕ) (y : ι → Fin 3 → ℤ)
    (j : ι) : SurfaceOccupiedResidueClass p y :=
  ⟨integralSurfaceResidue p (y j), ⟨j, rfl⟩⟩

/-- Every smooth occupied residue class contributes its exact first-jet
weight. All points and polynomials are literal; no charts, divisibility,
adapted weights, or section-existence statement is assumed. -/
theorem hypersurfaceAllResidue_det_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (hp : p.Prime)
    (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ)
    (hF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (hgrad : ∀ j, ∃ v, (MvPolynomial.eval (y j) (MvPolynomial.pderiv v F) : ZMod p) ≠ 0)
    (G : ι → MvPolynomial (Fin 3) ℤ) :
    (p : ℤ) ^ (∑ c : SurfaceOccupiedResidueClass p y,
      smoothSurfaceJetExponent (Fintype.card {j // surfacePointResidueClass p y j = c})) ∣
      (Matrix.of (fun i j => MvPolynomial.eval (y j) (G i))).det := by
  classical
  let cls := surfacePointResidueClass p y
  let rep : SurfaceOccupiedResidueClass p y → ι := fun c => c.property.choose
  have hrep (c : SurfaceOccupiedResidueClass p y) : cls (rep c) = c := by
    apply Subtype.ext
    exact c.property.choose_spec
  apply hypersurfaceResidueClasses_det_dvd p hp cls F y (fun c => y (rep c))
    (fun c => ⟨⟨rep c, hrep c⟩⟩) hF _ (fun c => hgrad (rep c)) G
  intro j i
  have hr := congrArg (fun c : SurfaceOccupiedResidueClass p y => c.val i) (hrep (cls j))
  change (y (rep (cls j)) i : ZMod p) = (y j i : ZMod p) at hr
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  push_cast
  exact sub_eq_zero.mpr hr.symm

end
end TranslatedDepthSeven
