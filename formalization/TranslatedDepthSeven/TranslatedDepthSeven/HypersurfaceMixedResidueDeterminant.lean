import TranslatedDepthSeven.HypersurfaceAllResidueDeterminant
import TranslatedDepthSeven.MixedSurfaceResidueDeterminant

/-! A literal all-residue determinant divisor for arbitrary hypersurface
points, including points with singular reduction. Only smooth residue
classes contribute, and no hypothesis is imposed on the remaining columns. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Actual smoothness of the affine hypersurface equation at the reduced
point, expressed by one nonzero partial derivative. -/
def surfaceGradientNonzeroMod (p : ℕ) (F : MvPolynomial (Fin 3) ℤ)
    (x : Fin 3 → ℤ) : Prop :=
  ∃ v : Fin 3, (MvPolynomial.eval x (MvPolynomial.pderiv v F) : ZMod p) ≠ 0

abbrev SmoothSurfaceColumn {ι : Type*} (p : ℕ) (F : MvPolynomial (Fin 3) ℤ)
    (y : ι → Fin 3 → ℤ) := {j // surfaceGradientNonzeroMod p F (y j)}

abbrev SurfaceOccupiedSmoothResidueClass {ι : Type*}
    (p : ℕ) (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ) :=
  SurfaceOccupiedResidueClass p (fun j : SmoothSurfaceColumn p F y => y j)

def smoothSurfacePointResidueClass {ι : Type*}
    (p : ℕ) (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ)
    (j : SmoothSurfaceColumn p F y) : SurfaceOccupiedSmoothResidueClass p F y :=
  surfacePointResidueClass p (fun j : SmoothSurfaceColumn p F y => y j) j

/-- The sum of the exact local exponents, over the occupied smooth classes
of the actual displayed integer columns. -/
def hypersurfaceSmoothResidueExponent {ι : Type*} [Fintype ι]
    (p : ℕ) (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ) : ℕ := by
  classical
  exact ∑ c : SurfaceOccupiedSmoothResidueClass p F y,
    smoothSurfaceJetExponent
      (Fintype.card {j // smoothSurfacePointResidueClass p F y j = c})

/-- Arbitrary integral points on the literal hypersurface: singular
reductions are retained as columns but contribute no local gain. -/
theorem hypersurfaceMixedResidue_det_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (hp : p.Prime)
    (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ)
    (hF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (G : ι → MvPolynomial (Fin 3) ℤ) :
    (p : ℤ) ^ hypersurfaceSmoothResidueExponent p F y ∣
      (Matrix.of (fun i j => MvPolynomial.eval (y j) (G i))).det := by
  classical
  let good : ι → Prop := fun j => surfaceGradientNonzeroMod p F (y j)
  let label := smoothSurfacePointResidueClass p F y
  let rep : SurfaceOccupiedSmoothResidueClass p F y → SmoothSurfaceColumn p F y :=
    fun c => c.property.choose
  have hrep (c : SurfaceOccupiedSmoothResidueClass p F y) : label (rep c) = c := by
    apply Subtype.ext
    exact c.property.choose_spec
  change (p : ℤ) ^ (∑ c, smoothSurfaceJetExponent (Fintype.card {j // label j = c})) ∣ _
  by_cases hE : 0 < ∑ c, smoothSurfaceJetExponent (Fintype.card {j // label j = c})
  · apply mixedSurfaceResidueDiscBlocks_det_dvd p good label y hE _ G
    intro c
    letI : Nonempty {j : SmoothSurfaceColumn p F y // label j = c} :=
      ⟨⟨rep c, hrep c⟩⟩
    let v := (rep c).property.choose
    have hv := (rep c).property.choose_spec
    apply surfaceHypersurfaceResidueDiscAt
      (ι := {j : SmoothSurfaceColumn p F y // label j = c})
      p _ hp hE F (fun j => y j.val.val) (y (rep c).val)
      (fun j => hF j.val.val) _ v hv
    intro j i
    have hc : label j.val = label (rep c) := j.property.trans (hrep c).symm
    have hr := congrArg (fun c : SurfaceOccupiedSmoothResidueClass p F y => c.val i) hc
    change (y j.val.val i : ZMod p) = (y (rep c).val i : ZMod p) at hr
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    exact sub_eq_zero.mpr hr
  · have hz : (∑ c, smoothSurfaceJetExponent (Fintype.card {j // label j = c})) = 0 :=
      Nat.eq_zero_of_not_pos hE
    simp only [hz, pow_zero, one_dvd]

/-- Distinct auxiliary primes may contribute different, internally
computed exponents. Their product divides the same integer determinant. -/
theorem hypersurfaceMixedResidue_primeProduct_det_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ)
    (hF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (G : ι → MvPolynomial (Fin 3) ℤ) :
    (∏ p ∈ P, (p : ℤ) ^ hypersurfaceSmoothResidueExponent p F y) ∣
      (Matrix.of (fun i j => MvPolynomial.eval (y j) (G i))).det := by
  apply primePowerProduct_dvd_of_local_divisibility P _ _ hP
  intro p hp
  exact hypersurfaceMixedResidue_det_dvd p (hP p hp) F y hF G

end
end TranslatedDepthSeven
