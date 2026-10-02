import CubicTenVariables.ReducedVertexBaseChange
import HessianTheorem11.PolynomialWeightTransport
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Adapted coordinates for the actual maximal cubic vertex. All coordinate
identities hold over finite fields as well as infinite fields. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.ReducedConeCoordinates
open MvPolynomial HessianTheorem11 PolynomialRestriction PolynomialWeightTransport
open ReducedCubicVertex Module Matrix
variable {K : Type*} [Field K] {n r m : ℕ}

/-- Three distinct scalars suffice for homogeneous cubic extensionality. -/
theorem three_le_card (h2 : (2 : K) ≠ 0) : (3 : Cardinal) ≤ Cardinal.mk K := by
  have h12 : (1 : K) ≠ 2 := by
    intro h
    have he := congrArg (fun z : K => z - 1) h
    norm_num at he
  have hi : Function.Injective (fun i : Fin 3 => (i.val : K)) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  simpa using Cardinal.lift_mk_le_lift_mk_of_injective hi

/-- Linear coordinates adapted to any subspace, with a base indexed by Fin. -/
theorem exists_adapted_equiv (W : Submodule K (Fin n → K)) :
    ∃ E : (Fin n → K) ≃ₗ[K]
        ((Fin (finrank K W) → K) × (Fin (n - finrank K W) → K)),
      ∀ x, (E x).2 = 0 ↔ x ∈ W := by
  classical
  obtain ⟨C, hC⟩ := W.exists_isCompl
  have hdim : finrank K C = n - finrank K W := by
    have h := Submodule.finrank_add_eq_of_isCompl hC
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    omega
  let bW := Module.finBasis K W
  let bC := (Module.finBasis K C).reindex (finCongr hdim)
  let E := (Submodule.prodEquivOfIsCompl W C hC).symm.trans
    (bW.equivFun.prodCongr bC.equivFun)
  refine ⟨E, ?_⟩
  intro x
  change bC.equivFun (((Submodule.prodEquivOfIsCompl W C hC).symm x).2) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero W C hC

/-- Projection to the nonvertex coordinates. -/
def projection (E : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin m → K))) :
    Matrix (Fin m) (Fin n) K :=
  LinearMap.toMatrix' ((LinearMap.snd K _ _).comp E.toLinearMap)

/-- The coordinate section sets the vertex coordinates equal to zero. -/
def sectionMatrix (E : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin m → K))) :
    Matrix (Fin n) (Fin m) K :=
  LinearMap.toMatrix' (E.symm.toLinearMap.comp (LinearMap.inr K _ _))

@[simp] theorem projection_mulVec (E : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin m → K)))
    (x : Fin n → K) : (projection E).mulVec x = (E x).2 := by
  simp [projection, LinearMap.toMatrix'_mulVec]

@[simp] theorem sectionMatrix_mulVec (E : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin m → K)))
    (x : Fin m → K) : (sectionMatrix E).mulVec x = E.symm (0,x) := by
  simp [sectionMatrix, LinearMap.toMatrix'_mulVec]

@[simp] theorem projection_section (E : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin m → K))) :
    projection E * sectionMatrix E = 1 := by
  apply Matrix.mulVec_injective
  funext x
  simp [← Matrix.mulVec_mulVec]

/-- The cubic factors through the quotient by its full actual vertex. -/
theorem exists_cone_coordinates (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    ∃ (E : (Fin n → K) ≃ₗ[K]
        ((Fin (finrank K (affineVertex F hF)) → K) ×
         (Fin (n - finrank K (affineVertex F hF)) → K)))
      (Q : MvPolynomial (Fin (n - finrank K (affineVertex F hF))) K)
      (hQ : Q.IsHomogeneous 3),
      (∀ x, (E x).2 = 0 ↔ x ∈ affineVertex F hF) ∧
      Q = restrict (sectionMatrix E) F ∧
      F = restrict (projection E) Q ∧
      (∀ x, eval x F = eval (E x).2 Q) ∧
      affineVertex Q hQ = ⊥ := by
  classical
  obtain ⟨E, hE⟩ := exists_adapted_equiv (affineVertex F hF)
  let Q := restrict (sectionMatrix E) F
  have hQ : Q.IsHomogeneous 3 := homogeneous_restrict _ F hF
  have heval (x : Fin n → K) : eval x F = eval (E x).2 Q := by
    have hv : x - E.symm (0,(E x).2) ∈ affineVertex F hF := by
      apply (hE _).mp
      simp only [map_sub, E.apply_symm_apply, Prod.snd_sub, sub_self]
    have ht := (mem_affineVertex_iff_translation F hF h2 h3 _).mp hv
    have he := ht (E.symm (0,(E x).2)) 1
    simpa [Q, eval_restrict] using he
  have hfactor : F = restrict (projection E) Q := by
    apply hF.funext_of_le_card (homogeneous_restrict _ Q hQ) _ (three_le_card h2)
    intro x
    simpa [eval_restrict] using heval x
  refine ⟨E,Q,hQ,hE,rfl,hfactor,heval,?_⟩
  apply bot_unique
  intro v hv
  change v = 0
  have hv' : TranslationDirection Q v :=
    (mem_affineVertex_iff_translation Q hQ h2 h3 v).mp hv
  have ht : TranslationDirection F (E.symm (0,v)) := by
    intro x t
    rw [heval, heval]
    simpa only [map_add, map_smul, E.apply_symm_apply, Prod.snd_add, Prod.smul_snd] using
      hv' (E x).2 t
  have hw := (mem_affineVertex_iff_translation F hF h2 h3 _).mpr ht
  simpa using (hE _).mpr hw

/-- A ring retraction descends primality of a principal ideal. -/
theorem principal_quotient_domain_of_retraction
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : S →+* R) (hg : Function.LeftInverse g f)
    (P : R) (h : IsDomain (S ⧸ Ideal.span {f P})) :
    IsDomain (R ⧸ Ideal.span {P}) := by
  have he : Ideal.span {P} = (Ideal.span {f P}).comap f := by
    ext a
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
    constructor
    · exact fun h => map_dvd f h
    · rintro ⟨b,hb⟩
      refine ⟨g b, ?_⟩
      simpa only [map_mul, hg a, hg P] using congrArg g hb
  apply (Ideal.Quotient.isDomain_iff_prime _).mpr
  letI : (Ideal.span {f P}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp h
  rw [he]
  infer_instance

/-- A polynomial retract descends the actual hypersurface domain property. -/
theorem quotient_domain_of_restrict
    (P : MvPolynomial (Fin m) K)
    (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin m) K)
    (hAB : A * B = 1)
    (h : IsDomain (MvPolynomial (Fin n) K ⧸ Ideal.span {restrict A P})) :
    IsDomain (MvPolynomial (Fin m) K ⧸ Ideal.span {P}) := by
  let f : MvPolynomial (Fin m) K →+* MvPolynomial (Fin n) K :=
    (aeval (linearForms A)).toRingHom
  let g : MvPolynomial (Fin n) K →+* MvPolynomial (Fin m) K :=
    (aeval (linearForms B)).toRingHom
  have hleft : Function.LeftInverse g f := by
    intro Q
    change restrict B (restrict A Q) = Q
    rw [restrict_restrict, hAB, restrict_one]
  exact principal_quotient_domain_of_retraction f g hleft P h

/-- The same descent holds after every field extension, in particular after
extension to an algebraic closure. -/
theorem quotient_domain_baseChange_of_factor
    {L : Type*} [Field L] [Algebra K L]
    (F : MvPolynomial (Fin n) K) (Q : MvPolynomial (Fin m) K)
    (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin m) K)
    (hAB : A * B = 1) (hFQ : F = restrict A Q)
    (h : IsDomain (MvPolynomial (Fin n) L ⧸
      Ideal.span {map (algebraMap K L) F})) :
    IsDomain (MvPolynomial (Fin m) L ⧸
      Ideal.span {map (algebraMap K L) Q}) := by
  apply quotient_domain_of_restrict (map (algebraMap K L) Q)
    (A.map (algebraMap K L)) (B.map (algebraMap K L))
  · rw [← Matrix.map_mul, hAB]
    simp
  · rw [hFQ, map_restrict] at h
    exact h

/-- Adapted-coordinate bases remain vertex-free over every field extension. -/
theorem vertex_baseChange_eq_bot
    {L : Type*} [Field L] [Algebra K L]
    (Q : MvPolynomial (Fin m) K) (hQ : Q.IsHomogeneous 3)
    (hv : affineVertex Q hQ = ⊥) :
    affineVertex (map (algebraMap K L) Q) (hQ.map _) = ⊥ :=
  (ReducedVertexBaseChange.affineVertex_baseChange_eq_bot_iff Q hQ).mpr hv

/-- There are no geometric translation directions in the base, not merely
no directions over its field of definition. -/
theorem translation_baseChange_eq_zero
    {L : Type*} [Field L] [Algebra K L]
    (Q : MvPolynomial (Fin m) K) (hQ : Q.IsHomogeneous 3)
    (h2 : (2 : K) ≠ 0) (hv : affineVertex Q hQ = ⊥)
    (v : Fin m → L)
    (ht : TranslationDirection (map (algebraMap K L) Q) v) : v = 0 := by
  have h2' : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h2
  have hmem : v ∈ affineVertex (map (algebraMap K L) Q) (hQ.map _) :=
    hessian_zero_of_translation _ (hQ.map _) h2' v ht
  rw [vertex_baseChange_eq_bot Q hQ hv] at hmem
  exact (Submodule.mem_bot L).mp hmem

end CubicTenVariables.ReducedConeCoordinates
