import CubicTenVariables.CubicSingularGeneralPosition
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! The actual projective singular-point set of a cubic surface and the
finiteness obstruction to a whole singular projective line. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.CubicSurfaceProjectiveSingular
open MvPolynomial HessianTheorem11
open scoped LinearAlgebra.Projectivization
variable {K : Type*} [Field K]

/-- Actual nonzero singular representatives, modulo scalar equivalence. -/
def singularPoints (F : MvPolynomial (Fin 4) K) : Set (ℙ K (Fin 4 → K)) :=
  {p | ∃ (x : Fin 4 → K) (hx : x ≠ 0),
    Projectivization.mk K x hx = p ∧ eval x F = 0 ∧ HessianTheorem11.gradient F x = 0}

theorem mk_mem_singularPoints (F : MvPolynomial (Fin 4) K)
    (x : Fin 4 → K) (hx : x ≠ 0) (hF : eval x F = 0)
    (hg : HessianTheorem11.gradient F x = 0) :
    Projectivization.mk K x hx ∈ singularPoints F := ⟨x,hx,rfl,hF,hg⟩

/-- Distinct projective points have representatives outside each other's
one-dimensional spans. -/
theorem not_mem_span_of_mk_ne (x y : Fin 4 → K) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Projectivization.mk K x hx ≠ Projectivization.mk K y hy) :
    x ∉ Submodule.span K ({y} : Set (Fin 4 → K)) := by
  intro hm
  apply h
  exact (Projectivization.mk_eq_mk_iff' K x y hx hy).mpr
    (Submodule.mem_span_singleton.mp hm)

/-- A finite actual projective singular locus contains no genuine singular
line. The proof injects the infinite field via the representatives B·(1,t). -/
theorem no_singular_line [Infinite K]
    (F : MvPolynomial (Fin 4) K) (hfin : (singularPoints F).Finite)
    (B : Matrix (Fin 4) (Fin 2) K) (hB : Function.Injective B.mulVec) :
    ¬ (∀ x : Fin 2 → K, eval (B.mulVec x) F = 0 ∧
      HessianTheorem11.gradient F (B.mulVec x) = 0) := by
  intro hline
  have hne (t : K) : B.mulVec ![1,t] ≠ 0 := by
    intro h
    have hv := hB (h.trans (Matrix.mulVec_zero B).symm)
    have h0 := congrFun hv 0
    simp at h0
  let f : K → ℙ K (Fin 4 → K) := fun t => Projectivization.mk K (B.mulVec ![1,t]) (hne t)
  have hinj : Function.Injective f := by
    intro s t hst
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ (hne s) (hne t)).mp hst
    have hv : a • (![1,t] : Fin 2 → K) = ![1,s] := by
      apply hB
      simpa only [Matrix.mulVec_smul] using ha
    have h0 := congrFun hv 0
    have ha1 : a = 1 := by simpa using h0
    have h1 := congrFun hv 1
    simpa [ha1] using h1.symm
  have hsubset : Set.range f ⊆ singularPoints F := by
    rintro p ⟨t,rfl⟩
    exact mk_mem_singularPoints F _ (hne t) (hline _).1 (hline _).2
  letI : Finite K := (Set.finite_range_iff hinj).mp (hfin.subset hsubset)
  exact not_finite K


/-- Matrix form of a literal finite vector family. -/
def pointMatrix {m : ℕ} (v : Fin m → Fin 4 → K) : Matrix (Fin 4) (Fin m) K :=
  fun i j => v j i

theorem pointMatrix_injective {m : ℕ} (v : Fin m → Fin 4 → K)
    (hv : LinearIndependent K v) : Function.Injective (pointMatrix v).mulVec :=
  Matrix.mulVec_injective_iff.mpr hv

@[simp] theorem pointMatrix_single {m : ℕ} (v : Fin m → Fin 4 → K) (i : Fin m) :
    (pointMatrix v).mulVec (Pi.single i 1) = v i := by
  rw [Matrix.mulVec_single_one]
  rfl

theorem no_singular_span_pair [Infinite K]
    (F : MvPolynomial (Fin 4) K) (hfin : (singularPoints F).Finite)
    (p q : Fin 4 → K) (hpq : LinearIndependent K ![p,q]) :
    ¬ (∀ s t : K, eval (s • p + t • q) F = 0 ∧
      HessianTheorem11.gradient F (s • p + t • q) = 0) := by
  intro hline
  apply no_singular_line F hfin (pointMatrix ![p,q]) (pointMatrix_injective _ hpq)
  intro x
  have he : (pointMatrix ![p,q]).mulVec x = x 0 • p + x 1 • q := by
    ext i
    simp [pointMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,smul_eq_mul,mul_comm]
  rw [he]
  exact hline _ _

end CubicTenVariables.CubicSurfaceProjectiveSingular
