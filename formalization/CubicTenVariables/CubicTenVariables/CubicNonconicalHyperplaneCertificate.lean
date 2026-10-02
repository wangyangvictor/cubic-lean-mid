import CubicTenVariables.CubicNonconicalMinorCertificate
import CubicTenVariables.GenericNonconicalHyperplane

/-! A polynomial certificate on the actual normal coordinates for
nonconical cubic hyperplane sections. A characteristic-zero nonconical
specialization constructs a nonzero Hessian minor in the coefficient ring.
Every field specialization preserving this polynomial gives an actual
injective kernel frame and a geometrically nonconical restriction, away
from characteristics two and three. No integrality or uniform degree claim. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.CubicNonconicalHyperplaneCertificate
open MvPolynomial HessianTheorem11 Matrix Literature
open HessianTheorem11.PolynomialRestriction
open GenericNormalDerivations CubicNonconicalMinorCertificate
open scoped BigOperators

def frame {R : Type*} [CommRing R] {n : ℕ} (u : Fin (n+1) → R) :
    Matrix (Fin (n+1)) (Fin n) R :=
  GenericHyperplaneFrameOpen.chartFrame u 1

theorem frame_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (u : Fin (n+1) → R) (ρ : R →+* S) :
    (frame u).map ρ = frame (fun i => ρ (u i)) := by
  classical
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [frame, GenericHyperplaneFrameOpen.chartFrame, Matrix.one_apply]
  · by_cases hij : i = j <;>
      simp [frame, GenericHyperplaneFrameOpen.chartFrame, Matrix.one_apply, hij]

theorem frame_injective {K : Type*} [Field K] {n : ℕ}
    (u : Fin (n+1) → K) (hu : u 0 ≠ 0) : Function.Injective (frame u).mulVec := by
  classical
  intro y z h
  ext i
  have he := congrFun h i.succ
  have he' : u 0 * y i = u 0 * z i := by
    simpa [frame, GenericHyperplaneFrameOpen.chartFrame, Matrix.mulVec, dotProduct,
      Matrix.one_apply] using he
  exact mul_left_cancel₀ hu he'

theorem frame_column {R : Type*} [CommRing R] {n : ℕ}
    (u : Fin (n+1) → R) (j : Fin n) : ∑ i, u i * frame u i j = 0 := by
  classical
  rw [Fin.sum_univ_succ]
  simp [frame, GenericHyperplaneFrameOpen.chartFrame, Matrix.one_apply, mul_comm]

theorem frame_range {K : Type*} [Field K] {n : ℕ}
    (u : Fin (n+1) → K) (hu : u 0 ≠ 0) :
    LinearMap.range (frame u).mulVecLin =
      LinearMap.ker (GenericHyperplaneFrameKernel.normal u) :=
  GenericHyperplaneFrameKernel.range_eq_ker u hu (frame u)
    (frame_injective u hu) (frame_column u)

def family {R : Type*} [CommRing R] {n : ℕ} (F : MvPolynomial (Fin (n+1)) R) :
    MvPolynomial (Fin n) (MvPolynomial (Fin (n+1)) R) :=
  restrict (frame X) (map C F)

theorem family_homogeneous {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous 3) :
    (family F).IsHomogeneous 3 := homogeneous_restrict _ _ (hF.map _)

theorem specialize_family {R K : Type*} [CommRing R] [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin (n+1)) R) (ρ : R →+* K) (u : Fin (n+1) → K) :
    map (eval₂Hom ρ u) (family F) = restrict (frame u) (map ρ F) := by
  have hc : (eval₂Hom ρ u).comp (C : R →+* MvPolynomial (Fin (n+1)) R) = ρ := by
    ext a
    simp
  rw [family, map_restrict, MvPolynomial.map_map, hc, frame_map]
  congr 1
  funext i
  simp

/-- The certificate is a normal coordinate times an actual maximal minor
of the restricted Hessian coefficient matrix. Its good characteristic-zero
specialization is nonzero; arbitrary later coefficient specializations are
allowed, including finite fields. -/
theorem exists_nonzero_certificate
    {R k : Type*} [CommRing R] [Field k] [CharZero k] {n : ℕ}
    (ρ : R →+* k) (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous 3)
    (hNC : GeometricallyNonconicalCubic (map ρ F)) :
    ∃ (rows : Fin n → Fin n × Fin n) (cols : Fin n → Fin n),
      let Δ := X 0 * minor (family F) rows cols
      map ρ Δ ≠ 0 ∧
      ∀ (K : Type*) [Field K] (τ : R →+* K) (u : Fin (n+1) → K),
        (2 : K) ≠ 0 → (3 : K) ≠ 0 → eval₂Hom τ u Δ ≠ 0 →
          Function.Injective (frame u).mulVec ∧
          LinearMap.range (frame u).mulVecLin =
            LinearMap.ker (GenericHyperplaneFrameKernel.normal u) ∧
          GeometricallyNonconicalCubic (restrict (frame u) (map τ F)) := by
  classical
  let Ω := GenericField k 1 (n+1)
  let u := genericNormal k 1 (n+1) 0
  let ρΩ : R →+* Ω := (algebraMap k Ω).comp ρ
  let ψ : MvPolynomial (Fin (n+1)) R →+* Ω := eval₂Hom ρΩ u
  have hu : u 0 ≠ 0 :=
    (map_ne_zero_iff _ (GenericNonconicalHyperplane.parameterMap_injective k 1 (n+1))).mpr
      (X_ne_zero _)
  have hγ : genericNormal k 1 (n+1) * frame u = 0 := by
    ext a j
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    exact frame_column u j
  have hgeneric : GeometricallyNonconicalCubic (map ψ (family F)) := by
    rw [show ψ = eval₂Hom ρΩ u from rfl, specialize_family]
    have h := GenericNonconicalHyperplane.generic_section_geometricallyNonconical
      (map ρ F) (hF.map _) hNC (frame u) (frame_injective u hu) hγ
    simpa only [MvPolynomial.map_map] using h
  obtain ⟨rows,cols,hminor,hgood⟩ := exists_minor_certificate
    (family F) (family_homogeneous F hF) ψ (by norm_num) (by norm_num) hgeneric
  refine ⟨rows,cols,?_,?_⟩
  · have he : ψ (X 0 * minor (family F) rows cols) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero (by simpa only [ψ, eval₂Hom_X'] using hu) hminor
    intro hz
    have hid : ψ (X 0 * minor (family F) rows cols) =
        eval₂Hom (algebraMap k Ω) u (map ρ (X 0 * minor (family F) rows cols)) :=
      (eval₂Hom_map_hom ρ u (algebraMap k Ω) _).symm
    exact he (by rw [hid,hz,map_zero])
  · intro K _ τ v h2 h3 hΔ
    have hh : v 0 ≠ 0 ∧ eval₂Hom τ v (minor (family F) rows cols) ≠ 0 := by
      simpa only [map_mul,eval₂Hom_X',mul_ne_zero_iff] using hΔ
    refine ⟨frame_injective v hh.1,frame_range v hh.1,?_⟩
    have h := hgood K (eval₂Hom τ v) h2 h3 hh.2
    rwa [specialize_family] at h

end CubicTenVariables.CubicNonconicalHyperplaneCertificate
