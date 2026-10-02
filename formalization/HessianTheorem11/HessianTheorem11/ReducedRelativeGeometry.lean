import HessianTheorem11.ReducedOrbitCoordinates
import HessianTheorem11.RationalDescent

/-! Coefficient-space orbit geometry and field conjugation.  The only geometric
input declared here is ordinary local closedness of an orbit, expressed as
closedness of its boundary.  All conjugation assertions are proved. -/
noncomputable section
namespace HessianTheorem11.ReducedRelative
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
variable {K : Type*} [Field K] {n : ℕ}

def coefficientVanishing (S : Set (MvPolynomial (Fin n) K))
    (P : MvPolynomial (Fin n →₀ ℕ) K) : Prop :=
  ∀ F ∈ S, eval (fun e => coeff e F) P = 0

def coefficientClosed (S : Set (MvPolynomial (Fin n) K)) : Prop :=
  ∀ F, (∀ P, coefficientVanishing S P → eval (fun e => coeff e F) P = 0) → F ∈ S

def orbitBoundary (F : MvPolynomial (Fin n) K) : Set (MvPolynomial (Fin n) K) :=
  slOrbitClosure F \ slOrbit F

def slInvariant (S : Set (MvPolynomial (Fin n) K)) : Prop :=
  ∀ A : Matrix (Fin n) (Fin n) K, A.det = 1 → ∀ F ∈ S, restrict A F ∈ S

theorem eval_coeff_map (σ : K ≃+* K) (F : MvPolynomial (Fin n) K)
    (P : MvPolynomial (Fin n →₀ ℕ) K) :
    eval (fun e => coeff e (map σ.toRingHom F)) (map σ.toRingHom P) =
      σ (eval (fun e => coeff e F) P) := by
  simpa only [coeff_map, Function.comp_def] using
    (MvPolynomial.map_eval σ.toRingHom (fun e => coeff e F) P).symm

@[simp] theorem map_symm_map (σ : K ≃+* K) {ι : Type*} (P : MvPolynomial ι K) :
    map σ.symm.toRingHom (map σ.toRingHom P) = P := by
  ext e
  simp only [coeff_map]
  exact σ.symm_apply_apply _

@[simp] theorem map_map_symm (σ : K ≃+* K) {ι : Type*} (P : MvPolynomial ι K) :
    map σ.toRingHom (map σ.symm.toRingHom P) = P := by
  ext e
  simp only [coeff_map]
  exact σ.apply_symm_apply _

theorem slOrbit_map (σ : K ≃+* K) (F G : MvPolynomial (Fin n) K)
    (hG : G ∈ slOrbit F) : map σ.toRingHom G ∈ slOrbit (map σ.toRingHom F) := by
  obtain ⟨A,hA,rfl⟩ := hG
  refine ⟨A.map σ.toRingHom, ?_, map_restrict _ _ _⟩
  change (σ.toRingHom.mapMatrix A).det = 1
  rw [← RingHom.map_det, hA, map_one]

theorem slOrbit_map_iff (σ : K ≃+* K) (F G : MvPolynomial (Fin n) K) :
    map σ.toRingHom G ∈ slOrbit (map σ.toRingHom F) ↔ G ∈ slOrbit F := by
  constructor
  · intro h
    simpa only [map_symm_map] using slOrbit_map σ.symm _ _ h
  · exact slOrbit_map σ F G

theorem slOrbitClosure_map (σ : K ≃+* K) (F G : MvPolynomial (Fin n) K)
    (hG : G ∈ slOrbitClosure F) :
    map σ.toRingHom G ∈ slOrbitClosure (map σ.toRingHom F) := by
  intro P hP
  have hz := hG (map σ.symm.toRingHom P) (by
    intro H hH
    apply σ.injective
    rw [map_zero, ← eval_coeff_map σ H (map σ.symm.toRingHom P), map_map_symm]
    exact hP _ (slOrbit_map σ F H hH))
  have he := eval_coeff_map σ G (map σ.symm.toRingHom P)
  rw [map_map_symm, hz, map_zero] at he
  exact he

theorem slOrbitClosure_map_iff (σ : K ≃+* K) (F G : MvPolynomial (Fin n) K) :
    map σ.toRingHom G ∈ slOrbitClosure (map σ.toRingHom F) ↔ G ∈ slOrbitClosure F := by
  constructor
  · intro h
    simpa only [map_symm_map] using slOrbitClosure_map σ.symm _ _ h
  · exact slOrbitClosure_map σ F G

theorem orbitBoundary_map_iff (σ : K ≃+* K) (F G : MvPolynomial (Fin n) K) :
    map σ.toRingHom G ∈ orbitBoundary (map σ.toRingHom F) ↔ G ∈ orbitBoundary F := by
  simp only [orbitBoundary, Set.mem_diff, slOrbitClosure_map_iff, slOrbit_map_iff]

theorem self_notMem_orbitBoundary (F : MvPolynomial (Fin n) K) : F ∉ orbitBoundary F :=
  fun h => h.2 (self_mem_slOrbit F)

theorem orbitBoundary_nonempty (F : MvPolynomial (Fin n) K)
    (hF : ¬ ClosedSLOrbit F) : (orbitBoundary F).Nonempty := by
  classical
  change ¬ (∀ G, G ∈ slOrbitClosure F → G ∈ slOrbit F) at hF
  push_neg at hF
  obtain ⟨G,hG,hn⟩ := hF
  exact ⟨G,hG,hn⟩

theorem orbitBoundary_invariant {d : ℕ} (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) : slInvariant (orbitBoundary F) := by
  intro A hA G hG
  have hunit : IsUnit A.det := hA ▸ isUnit_one
  refine ⟨?_, ?_⟩
  · intro P hP
    apply ReducedOrbitCoordinates.slOrbitClosure_restrict A hunit F G hF hG.1 P
    intro Q hQ
    obtain ⟨B,hB,rfl⟩ := hQ
    apply hP
    exact ⟨A*B, by rw [Matrix.det_mul,hA,hB,one_mul], by rw [restrict_restrict]⟩
  · intro h
    apply hG.2
    obtain ⟨B,hB,hBG⟩ := h
    refine ⟨B*A⁻¹, ?_, ?_⟩
    · rw [Matrix.det_mul,hB,one_mul,Matrix.det_nonsing_inv,hA,Ring.inverse_one]
    · have he := congrArg (restrict A⁻¹) hBG
      simpa only [restrict_restrict,Matrix.mul_nonsing_inv A hunit,restrict_one] using he

/-- Ordinary local closedness of orbits of an algebraic group action, on the
finite-dimensional representation of degree-d forms.  No weights, limits,
canonical flags, rationality, or cubic hypothesis occurs in this input. -/
structure OrbitBoundaryClosedInput (K : Type*) [Field K] [IsAlgClosed K] : Prop where
  closed_boundary : ∀ {n d : ℕ} (F : MvPolynomial (Fin n) K),
    F.IsHomogeneous d → coefficientClosed (orbitBoundary F)

end HessianTheorem11.ReducedRelative
