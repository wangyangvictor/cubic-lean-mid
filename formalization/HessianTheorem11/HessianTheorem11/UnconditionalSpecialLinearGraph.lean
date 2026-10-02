import HessianTheorem11.AffineGeometry
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! The reciprocal graph of a nonzero polynomial is an actual irreducible
closed affine set. It is identified with the zero locus of the prime kernel
of evaluation in the polynomial localization. -/
noncomputable section
namespace HessianTheorem11.UnconditionalSpecialLinear
open MvPolynomial
open scoped nonZeroDivisors

variable {σ : Type*}

def reciprocalGraph (q : MvPolynomial σ GeometricField) :
    Set ((σ ⊕ Unit) → GeometricField) :=
  {y | eval (y ∘ Sum.inl) q * y (Sum.inr ()) = 1}

def reciprocalEquation (q : MvPolynomial σ GeometricField) :
    MvPolynomial (σ ⊕ Unit) GeometricField :=
  rename Sum.inl q * X (Sum.inr ()) - 1

def reciprocalLocalizationMap (q : MvPolynomial σ GeometricField) :
    MvPolynomial (σ ⊕ Unit) GeometricField →ₐ[GeometricField] Localization.Away q :=
  aeval (Sum.elim (fun i => algebraMap (MvPolynomial σ GeometricField) (Localization.Away q) (X i))
    (fun _ => IsLocalization.Away.invSelf q))

@[simp] theorem reciprocalLocalizationMap_rename
    (q p : MvPolynomial σ GeometricField) :
    reciprocalLocalizationMap q (rename Sum.inl p) =
      algebraMap (MvPolynomial σ GeometricField) (Localization.Away q) p := by
  have h : aeval (fun i : σ => algebraMap (MvPolynomial σ GeometricField)
      (Localization.Away q) (X i)) =
      IsScalarTower.toAlgHom GeometricField (MvPolynomial σ GeometricField) (Localization.Away q) := by
    ext i
    simp
  change aeval _ (rename Sum.inl p) = _
  rw [aeval_rename]
  exact AlgHom.congr_fun h p

@[simp] theorem reciprocalEquation_map (q : MvPolynomial σ GeometricField) :
    reciprocalLocalizationMap q (reciprocalEquation q) = 0 := by
  rw [reciprocalEquation,map_sub,map_mul,reciprocalLocalizationMap_rename,map_one]
  simp only [reciprocalLocalizationMap,aeval_X,Sum.elim_inr]
  change algebraMap (MvPolynomial σ GeometricField) (Localization.Away q) q *
    IsLocalization.Away.invSelf q - 1 = 0
  rw [IsLocalization.Away.mul_invSelf,sub_self]

/-- The explicit reciprocal equation defines exactly the prime-kernel
point locus of localization, with no appeal to rational-map geometry. -/
theorem reciprocalGraph_eq_zeroLocus (q : MvPolynomial σ GeometricField) :
    reciprocalGraph q = zeroLocus GeometricField (RingHom.ker (reciprocalLocalizationMap q)) := by
  ext y
  constructor
  · intro hy p hp
    have hq : eval (y ∘ Sum.inl) q ≠ 0 := by
      intro hz
      have h := hy
      change eval (y ∘ Sum.inl) q * y (Sum.inr ()) = 1 at h
      rw [hz,zero_mul] at h
      exact zero_ne_one h
    let ψ : Localization.Away q →+* GeometricField :=
      IsLocalization.Away.lift q (g := eval (y ∘ Sum.inl)) (isUnit_iff_ne_zero.mpr hq)
    have hinv : ψ (IsLocalization.Away.invSelf q) = y (Sum.inr ()) := by
      apply mul_left_cancel₀ hq
      have h := congrArg ψ (IsLocalization.Away.mul_invSelf q (S := Localization.Away q))
      rw [map_mul,map_one,IsLocalization.Away.lift_eq] at h
      exact h.trans hy.symm
    have he : ψ.comp (reciprocalLocalizationMap q).toRingHom = eval y := by
      apply MvPolynomial.ringHom_ext
      · intro a
        change ψ (reciprocalLocalizationMap q (C a)) = eval y (C a)
        rw [show reciprocalLocalizationMap q (C a) =
          algebraMap GeometricField (Localization.Away q) a from
            (reciprocalLocalizationMap q).commutes a,eval_C]
        rw [IsScalarTower.algebraMap_apply GeometricField (MvPolynomial σ GeometricField)
          (Localization.Away q)]
        simpa [ψ] using (IsLocalization.Away.lift_eq (S := Localization.Away q) q
          (g := eval (y ∘ Sum.inl)) (isUnit_iff_ne_zero.mpr hq) (C a))
      · intro i
        change ψ (reciprocalLocalizationMap q (X i)) = eval y (X i)
        rw [eval_X]
        cases i with
        | inl i =>
          simp only [reciprocalLocalizationMap,aeval_X,Sum.elim_inl]
          simp [ψ]
        | inr i =>
          cases i
          simpa only [reciprocalLocalizationMap,aeval_X,Sum.elim_inr] using hinv
    have h := congrArg ψ (show reciprocalLocalizationMap q p = 0 from hp)
    rw [map_zero] at h
    exact (RingHom.congr_fun he p).symm.trans h
  · intro hy
    have h := hy (reciprocalEquation q) (reciprocalEquation_map q)
    simpa [reciprocalEquation,eval_rename,reciprocalGraph,sub_eq_zero] using h

theorem reciprocalGraph_closed (q : MvPolynomial σ GeometricField) :
    AlgebraicallyClosedSet (reciprocalGraph q) := by
  rw [reciprocalGraph_eq_zeroLocus]
  exact algebraicallyClosedSet_zeroLocus _

/-- The source graph is irreducible because localization of the actual
polynomial domain at powers of a nonzero polynomial is again a domain. -/
theorem reciprocalGraph_irreducible [Fintype σ]
    (q : MvPolynomial σ GeometricField) (hq : q ≠ 0) :
    GeometricallyIrreducible (reciprocalGraph q) := by
  letI : IsDomain (Localization.Away q) := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hq)
  letI : (RingHom.ker (reciprocalLocalizationMap q)).IsPrime := RingHom.ker_isPrime _
  rw [reciprocalGraph_eq_zeroLocus]
  change (vanishingIdeal GeometricField (zeroLocus GeometricField
    (RingHom.ker (reciprocalLocalizationMap q)))).IsPrime
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]
  infer_instance

end HessianTheorem11.UnconditionalSpecialLinear
