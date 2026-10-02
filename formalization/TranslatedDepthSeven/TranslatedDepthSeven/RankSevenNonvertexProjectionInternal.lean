import TranslatedDepthSeven.RankSevenSourceSectionVertexInternal
import TranslatedDepthSeven.ProjectiveLinearSpanIsolation
import TranslatedDepthSeven.GaloisInvariantComponentPointDescent

/-!
# The nonvertex translated-cone projection, internally

This file replaces the bespoke degree-one nonvertex projection premise by
the literal homogeneous elimination which it abbreviates.  After the
translated cone is returned to coordinate-cone form, a row whose value at
the vertex is nonzero is monic in the vertex coordinate.  Substitution for
that coordinate identifies the source section, scheme-theoretically, with
the displayed three-row section.  The substitution and its section preserve
homogeneous degree, so the homogeneous Hilbert function is unchanged.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 8000000

universe u v

variable {K : Type u} [Field K] {σ : Type v}

/-- Substitute a homogeneous linear form for the distinguished `none`
coordinate and leave all spatial coordinates fixed. -/
def optionLinearEliminationAlgHom (l : MvPolynomial σ K) :
    MvPolynomial (Option σ) K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval fun o ↦ o.elim l MvPolynomial.X

@[simp]
theorem optionLinearEliminationAlgHom_X_none
    (l : MvPolynomial σ K) :
    optionLinearEliminationAlgHom l (MvPolynomial.X none) = l := by
  simp [optionLinearEliminationAlgHom]

@[simp]
theorem optionLinearEliminationAlgHom_X_some
    (l : MvPolynomial σ K) (i : σ) :
    optionLinearEliminationAlgHom l (MvPolynomial.X (some i)) =
      MvPolynomial.X i := by
  simp [optionLinearEliminationAlgHom]

@[simp]
theorem optionLinearEliminationAlgHom_C
    (l : MvPolynomial σ K) (a : K) :
    optionLinearEliminationAlgHom l (MvPolynomial.C a) =
      MvPolynomial.C a := by
  simp [optionLinearEliminationAlgHom]

@[simp]
theorem optionLinearEliminationAlgHom_rename_some
    (l : MvPolynomial σ K) (f : MvPolynomial σ K) :
    optionLinearEliminationAlgHom l (MvPolynomial.rename some f) = f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf => simp [hf]

theorem optionLinearEliminationAlgHom_surjective
    (l : MvPolynomial σ K) :
    Function.Surjective (optionLinearEliminationAlgHom l) := by
  intro f
  exact ⟨MvPolynomial.rename some f,
    optionLinearEliminationAlgHom_rename_some l f⟩

/-- The kernel of homogeneous substitution is the single displayed linear
equation. -/
theorem ker_optionLinearEliminationAlgHom
    (l : MvPolynomial σ K) :
    RingHom.ker (optionLinearEliminationAlgHom l) =
      Ideal.span ({MvPolynomial.X none - MvPolynomial.rename some l} :
        Set (MvPolynomial (Option σ) K)) := by
  let E := MvPolynomial.optionEquivLeft K σ
  let ev := Polynomial.evalRingHom l
  have hcomp : (optionLinearEliminationAlgHom l).toRingHom =
      ev.comp E.toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change optionLinearEliminationAlgHom l (MvPolynomial.C a) =
        Polynomial.eval l (MvPolynomial.optionEquivLeft K σ
          (MvPolynomial.C a))
      rw [MvPolynomial.optionEquivLeft_C, Polynomial.eval_C]
      simp [optionLinearEliminationAlgHom]
    · intro o
      cases o with
      | none =>
          change optionLinearEliminationAlgHom l (MvPolynomial.X none) =
            Polynomial.eval l (MvPolynomial.optionEquivLeft K σ
              (MvPolynomial.X none))
          rw [MvPolynomial.optionEquivLeft_X_none, Polynomial.eval_X]
          exact optionLinearEliminationAlgHom_X_none l
      | some i =>
          change optionLinearEliminationAlgHom l (MvPolynomial.X (some i)) =
            Polynomial.eval l (MvPolynomial.optionEquivLeft K σ
              (MvPolynomial.X (some i)))
          rw [MvPolynomial.optionEquivLeft_X_some, Polynomial.eval_C]
          exact optionLinearEliminationAlgHom_X_some l i
  have hmap :
      (Ideal.span ({MvPolynomial.X none - MvPolynomial.rename some l} :
        Set (MvPolynomial (Option σ) K))).map E =
        Ideal.span ({Polynomial.X - Polynomial.C l} :
          Set (Polynomial (MvPolynomial σ K))) := by
    rw [Ideal.map_span]
    congr 2
    simp only [Set.image_singleton, map_sub, E,
      MvPolynomial.optionEquivLeft_X_none,
      optionEquivLeft_rename_some]
  calc
    RingHom.ker (optionLinearEliminationAlgHom l).toRingHom =
        (RingHom.ker ev).comap E := by
      rw [hcomp]
      ext f
      simp only [RingHom.mem_ker, Ideal.mem_comap]
      rfl
    _ = (Ideal.span ({Polynomial.X - Polynomial.C l} :
          Set (Polynomial (MvPolynomial σ K)))).comap E := by
      rw [Polynomial.ker_evalRingHom]
    _ = Ideal.span ({MvPolynomial.X none - MvPolynomial.rename some l} :
          Set (MvPolynomial (Option σ) K)) := by
      rw [← hmap]
      exact Ideal.comap_map_of_bijective E E.bijective

/-- Substitution by a degree-one form preserves every homogeneous degree. -/
theorem optionLinearEliminationAlgHom_isHomogeneous
    (l : MvPolynomial σ K) (hl : l.IsHomogeneous 1)
    {f : MvPolynomial (Option σ) K} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    (optionLinearEliminationAlgHom l f).IsHomogeneous d := by
  convert hf.aeval (fun o ↦ o.elim l MvPolynomial.X) (by
    intro o
    cases o with
    | none => exact hl
    | some i => exact MvPolynomial.isHomogeneous_X (R := K) i) using 1 <;>
    simp [optionLinearEliminationAlgHom]

/-- The quotient equivalence induced by homogeneous elimination. -/
def optionLinearEliminationQuotientAlgEquiv
    (l : MvPolynomial σ K) (Q : Ideal (MvPolynomial σ K)) :
    (MvPolynomial (Option σ) K ⧸
      Q.comap (optionLinearEliminationAlgHom l)) ≃ₐ[K]
        (MvPolynomial σ K ⧸ Q) := by
  let f : MvPolynomial (Option σ) K →ₐ[K]
      (MvPolynomial σ K ⧸ Q) :=
    (Ideal.Quotient.mkₐ K Q).comp (optionLinearEliminationAlgHom l)
  have hf : Function.Surjective f :=
    (Ideal.Quotient.mkₐ_surjective K Q).comp
      (optionLinearEliminationAlgHom_surjective l)
  have hker : RingHom.ker f =
      Q.comap (optionLinearEliminationAlgHom l) := by
    ext g
    simp [f, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  exact (Ideal.quotientEquivAlgOfEq K hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)

@[simp]
theorem optionLinearEliminationQuotientAlgEquiv_mk
    (l : MvPolynomial σ K) (Q : Ideal (MvPolynomial σ K))
    (f : MvPolynomial (Option σ) K) :
    optionLinearEliminationQuotientAlgEquiv l Q
        (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk Q (optionLinearEliminationAlgHom l f) := by
  simp [optionLinearEliminationQuotientAlgEquiv]

/-! ## Homogeneous Hilbert functions under a split surjection -/

universe w

/-- A surjective polynomial algebra map identifies the quotient by the
inverse image of an ideal with the target quotient. -/
def surjectiveComapQuotientAlgEquiv
    {ι : Type v} {κ : Type w}
    (f : MvPolynomial ι K →ₐ[K] MvPolynomial κ K)
    (hf : Function.Surjective f)
    (Q : Ideal (MvPolynomial κ K)) :
    (MvPolynomial ι K ⧸ Q.comap f) ≃ₐ[K]
      (MvPolynomial κ K ⧸ Q) := by
  let g : MvPolynomial ι K →ₐ[K] (MvPolynomial κ K ⧸ Q) :=
    (Ideal.Quotient.mkₐ K Q).comp f
  have hg : Function.Surjective g :=
    (Ideal.Quotient.mkₐ_surjective K Q).comp hf
  have hker : RingHom.ker g = Q.comap f := by
    ext p
    simp [g, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  exact (Ideal.quotientEquivAlgOfEq K hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hg)

@[simp]
theorem surjectiveComapQuotientAlgEquiv_mk
    {ι : Type v} {κ : Type w}
    (f : MvPolynomial ι K →ₐ[K] MvPolynomial κ K)
    (hf : Function.Surjective f)
    (Q : Ideal (MvPolynomial κ K))
    (p : MvPolynomial ι K) :
    surjectiveComapQuotientAlgEquiv f hf Q
        (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk Q (f p) := by
  simp [surjectiveComapQuotientAlgEquiv]

/-- A split surjection given by degree-one substitutions carries the
degree-`k` quotient piece onto the degree-`k` quotient piece. -/
theorem quotientHomogeneousComponent_comap_surjective
    {ι : Type v} {κ : Type w}
    (f : MvPolynomial ι K →ₐ[K] MvPolynomial κ K)
    (hf : Function.Surjective f)
    (g : MvPolynomial κ K →ₐ[K] MvPolynomial ι K)
    (hright : f.comp g = AlgHom.id K (MvPolynomial κ K))
    (hfhom : ∀ (d : ℕ) (p : MvPolynomial ι K),
      p.IsHomogeneous d → (f p).IsHomogeneous d)
    (hghom : ∀ (d : ℕ) (p : MvPolynomial κ K),
      p.IsHomogeneous d → (g p).IsHomogeneous d)
    (Q : Ideal (MvPolynomial κ K)) (d : ℕ) :
    (quotientHomogeneousComponent K ι (Q.comap f) d).map
        (surjectiveComapQuotientAlgEquiv f hf Q).toLinearMap =
      quotientHomogeneousComponent K κ Q d := by
  ext z
  constructor
  · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨f p, hfhom d p hp, ?_⟩
    exact surjectiveComapQuotientAlgEquiv_mk f hf Q p
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Ideal.Quotient.mk (Q.comap f) (g p), ?_, ?_⟩
    · exact ⟨g p, hghom d p hp, rfl⟩
    · change surjectiveComapQuotientAlgEquiv f hf Q
          (Ideal.Quotient.mk (Q.comap f) (g p)) =
        Ideal.Quotient.mk Q p
      rw [surjectiveComapQuotientAlgEquiv_mk]
      have hpRight := DFunLike.congr_fun hright p
      simpa using congrArg (Ideal.Quotient.mk Q) hpRight

/-- Consequently every homogeneous quotient piece has the same finite
dimension on the two sides. -/
theorem finrank_quotientHomogeneousComponent_comap_surjective
    {ι : Type v} {κ : Type w} [Finite ι] [Finite κ]
    (f : MvPolynomial ι K →ₐ[K] MvPolynomial κ K)
    (hf : Function.Surjective f)
    (g : MvPolynomial κ K →ₐ[K] MvPolynomial ι K)
    (hright : f.comp g = AlgHom.id K (MvPolynomial κ K))
    (hfhom : ∀ (d : ℕ) (p : MvPolynomial ι K),
      p.IsHomogeneous d → (f p).IsHomogeneous d)
    (hghom : ∀ (d : ℕ) (p : MvPolynomial κ K),
      p.IsHomogeneous d → (g p).IsHomogeneous d)
    (Q : Ideal (MvPolynomial κ K)) (d : ℕ) :
    Module.finrank K
        (quotientHomogeneousComponent K ι (Q.comap f) d) =
      Module.finrank K (quotientHomogeneousComponent K κ Q d) := by
  rw [← quotientHomogeneousComponent_comap_surjective
    f hf g hright hfhom hghom Q d]
  exact (LinearEquiv.finrank_map_eq
    (surjectiveComapQuotientAlgEquiv f hf Q).toLinearEquiv
      (quotientHomogeneousComponent K ι (Q.comap f) d)).symm

/-- A split homogeneous surjection preserves the complete projective
dimension--degree certificate.  This is an internal graded-algebra fact,
not a geometric input. -/
theorem hasProjectiveDimensionDegree_comap_surjective_iff
    {Ns Nt : ℕ}
    (f : MvPolynomial (Fin (Ns + 1)) K →ₐ[K]
      MvPolynomial (Fin (Nt + 1)) K)
    (hf : Function.Surjective f)
    (g : MvPolynomial (Fin (Nt + 1)) K →ₐ[K]
      MvPolynomial (Fin (Ns + 1)) K)
    (hright : f.comp g = AlgHom.id K _)
    (hfhom : ∀ (d : ℕ) (p : MvPolynomial (Fin (Ns + 1)) K),
      p.IsHomogeneous d → (f p).IsHomogeneous d)
    (hghom : ∀ (d : ℕ) (p : MvPolynomial (Fin (Nt + 1)) K),
      p.IsHomogeneous d → (g p).IsHomogeneous d)
    (Q : Ideal (MvPolynomial (Fin (Nt + 1)) K))
    (r degree : ℕ) :
    HasProjectiveDimensionDegree (Q.comap f) r degree ↔
      HasProjectiveDimensionDegree Q r degree := by
  have hdim : ringKrullDim
      (MvPolynomial (Fin (Ns + 1)) K ⧸ Q.comap f) =
      ringKrullDim (MvPolynomial (Fin (Nt + 1)) K ⧸ Q) :=
    ringKrullDim_eq_of_ringEquiv
      (surjectiveComapQuotientAlgEquiv f hf Q).toRingEquiv
  constructor
  · rintro ⟨hkrull, hdegree, P, hPdegree, hPleading, k₀, hP⟩
    refine ⟨hdim ▸ hkrull, hdegree, P, hPdegree, hPleading, k₀, ?_⟩
    intro k hk
    change (Module.finrank K
      (quotientHomogeneousComponent K (Fin (Nt + 1)) Q k) : ℚ) = _
    rw [← finrank_quotientHomogeneousComponent_comap_surjective
      f hf g hright hfhom hghom Q k]
    simpa only [Published.projectiveHilbertPiece] using hP k hk
  · rintro ⟨hkrull, hdegree, P, hPdegree, hPleading, k₀, hP⟩
    refine ⟨hdim.trans hkrull, hdegree, P, hPdegree, hPleading, k₀, ?_⟩
    intro k hk
    change (Module.finrank K
      (quotientHomogeneousComponent K (Fin (Ns + 1)) (Q.comap f) k) : ℚ) = _
    rw [finrank_quotientHomogeneousComponent_comap_surjective
      f hf g hright hfhom hghom Q k]
    simpa only [Published.projectiveHilbertPiece] using hP k hk

/-! ## Literal elimination of a nonvertex four-row section -/

/-- Coefficients of a cutting row after the translated cone is returned to
coordinate-cone form.  The distinguished coefficient is the row's vertex
evaluation divided by `m`; the spatial coefficients are its old spatial
coefficients divided by `m`. -/
def translatedConeCoordinateSectionMatrix
    {c N : ℕ} (b : Fin N → K) (m : K)
    (A : Matrix (Fin c) (Option (Fin N)) K) :
    Matrix (Fin c) (Option (Fin N)) K
  | i, none => m⁻¹ *
      (m * A i none - ∑ j, A i (some j) * b j)
  | i, some j => m⁻¹ * A i (some j)

/-- The exact row formula under the inverse translated-cone coordinate
change. -/
theorem homogeneousAffinePolynomialChange_symm_matrixRow
    {c N : ℕ} (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin c) (Option (Fin N)) K) (i : Fin c) :
    (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm
        (indexedMatrixRowLinearPolynomial A i) =
      indexedMatrixRowLinearPolynomial
        (translatedConeCoordinateSectionMatrix b m A) i := by
  unfold indexedMatrixRowLinearPolynomial
    translatedConeCoordinateSectionMatrix
  rw [Fintype.sum_option]
  simp only [map_add, map_mul, map_sum,
    homogeneousAffinePolynomialChangeAlgEquiv_symm_C,
    homogeneousAffinePolynomialChangeAlgEquiv_symm_X_none,
    homogeneousAffinePolynomialChangeAlgEquiv_symm_X_some,
    Option.elim_none, Option.elim_some]
  calc
    MvPolynomial.C (A i none) * MvPolynomial.X none +
        ∑ x, MvPolynomial.C (A i (some x)) *
          (MvPolynomial.C m⁻¹ *
            (MvPolynomial.X (some x) -
              MvPolynomial.C (b x) * MvPolynomial.X none)) =
      (∑ x, MvPolynomial.C (m⁻¹ * A i (some x)) *
          MvPolynomial.X (some x)) +
        (MvPolynomial.C (A i none) -
          ∑ x, MvPolynomial.C (m⁻¹ * A i (some x) * b x)) *
            MvPolynomial.X none := by
      have hterm (x : Fin N) :
          MvPolynomial.C (A i (some x)) *
              (MvPolynomial.C m⁻¹ *
                (MvPolynomial.X (some x) -
                  MvPolynomial.C (b x) * MvPolynomial.X none)) =
            MvPolynomial.C (m⁻¹ * A i (some x)) *
                MvPolynomial.X (some x) -
              MvPolynomial.C (m⁻¹ * A i (some x) * b x) *
                MvPolynomial.X none := by
        have h₁ : MvPolynomial.C (A i (some x)) * MvPolynomial.C m⁻¹ =
            (MvPolynomial.C (m⁻¹ * A i (some x)) :
              MvPolynomial (Option (Fin N)) K) := by
          rw [← map_mul]
          congr 1
          ring
        have h₂ :
            MvPolynomial.C (m⁻¹ * A i (some x)) *
                MvPolynomial.C (b x) =
              (MvPolynomial.C (m⁻¹ * A i (some x) * b x) :
                MvPolynomial (Option (Fin N)) K) := by
          exact (map_mul MvPolynomial.C
            (m⁻¹ * A i (some x)) (b x)).symm
        calc
          MvPolynomial.C (A i (some x)) *
              (MvPolynomial.C m⁻¹ *
                (MvPolynomial.X (some x) -
                  MvPolynomial.C (b x) * MvPolynomial.X none)) =
            (MvPolynomial.C (A i (some x)) * MvPolynomial.C m⁻¹) *
                MvPolynomial.X (some x) -
              (MvPolynomial.C (A i (some x)) * MvPolynomial.C m⁻¹ *
                MvPolynomial.C (b x)) * MvPolynomial.X none := by ring
          _ = _ := by rw [h₁, h₂]
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib]
      rw [← Finset.sum_mul]
      ring
    _ = MvPolynomial.C
          (m⁻¹ * (m * A i none - ∑ x, A i (some x) * b x)) *
            MvPolynomial.X none +
        ∑ x, MvPolynomial.C (m⁻¹ * A i (some x)) *
          MvPolynomial.X (some x) := by
      have hcoeff :
          (MvPolynomial.C (A i none) -
              ∑ x, MvPolynomial.C (m⁻¹ * A i (some x) * b x) :
                MvPolynomial (Option (Fin N)) K) =
            MvPolynomial.C
              (m⁻¹ * (m * A i none - ∑ x, A i (some x) * b x)) := by
        rw [← map_sum, ← map_sub]
        congr 1
        have hsum :
            (∑ x, m⁻¹ * A i (some x) * b x) =
              m⁻¹ * (∑ x, A i (some x) * b x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
        rw [hsum]
        field_simp [hm]
      rw [hcoeff]
      exact add_comm _ _
    _ = ∑ j,
        MvPolynomial.C
          (translatedConeCoordinateSectionMatrix b m A i j) *
            MvPolynomial.X j := by
      rw [Fintype.sum_option]
      rfl

/-- Hence the complete row ideal is transported to the row ideal of the
displayed transformed matrix. -/
theorem map_indexedMatrixRowLinearIdeal_homogeneousAffine_symm
    {c N : ℕ} (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin c) (Option (Fin N)) K) :
    (indexedMatrixRowLinearIdeal A).map
        (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm =
      indexedMatrixRowLinearIdeal
        (translatedConeCoordinateSectionMatrix b m A) := by
  unfold indexedMatrixRowLinearIdeal
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, homogeneousAffinePolynomialChange_symm_matrixRow
      b m hm A i |>.symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨indexedMatrixRowLinearPolynomial A i, ⟨i, rfl⟩, ?_⟩
    exact homogeneousAffinePolynomialChange_symm_matrixRow b m hm A i

/-- The whole cone-plus-row ideal after returning the translated cone to
coordinate-cone form. -/
theorem map_translatedCone_sup_rows_homogeneousAffine_symm
    {c N : ℕ} (J : Ideal (MvPolynomial (Fin N) K))
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin c) (Option (Fin N)) K) :
    (translatedProjectiveConeIdeal b m hm J ⊔
        indexedMatrixRowLinearIdeal A).map
        (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm =
      projectiveConeIdealExtension J ⊔
        indexedMatrixRowLinearIdeal
          (translatedConeCoordinateSectionMatrix b m A) := by
  rw [Ideal.map_sup,
    map_indexedMatrixRowLinearIdeal_homogeneousAffine_symm]
  unfold translatedProjectiveConeIdeal
  let T := homogeneousAffinePolynomialChangeAlgEquiv b m hm
  have hcone : ((projectiveConeIdealExtension J).map T).map T.symm =
      projectiveConeIdealExtension J :=
    Ideal.map_of_equiv T.toRingEquiv
  exact congrArg (fun L ↦ L ⊔
    indexedMatrixRowLinearIdeal
      (translatedConeCoordinateSectionMatrix b m A)) hcone

/-! ## Elimination of a displayed nonvertex pivot -/

/-- The linear form substituted for the distinguished coordinate after a
nonzero row has been selected. -/
def translatedConePivotEliminationForm
    (b : Fin 13 → ℚ) (m : ℚ)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4) :
    MvPolynomial (Fin 13) ℚ :=
  -MvPolynomial.C (translatedJoinVertexEvaluation A b m i₀)⁻¹ *
    indexedMatrixRowLinearPolynomial
      (projectiveSectionSpatialMatrix A) i₀

theorem translatedConePivotEliminationForm_isHomogeneous
    (b : Fin 13 → ℚ) (m : ℚ)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4) :
    (translatedConePivotEliminationForm b m A i₀).IsHomogeneous 1 := by
  unfold translatedConePivotEliminationForm
  rw [← map_neg]
  exact (indexedMatrixRowLinearPolynomial_isHomogeneous
    (projectiveSectionSpatialMatrix A) i₀).C_mul _

/-- A transformed row, after substituting for the distinguished
coordinate, written in terms of its vertex evaluation and spatial row. -/
theorem optionLinearElimination_transformedRow_apply
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ i : Fin 4) :
    optionLinearEliminationAlgHom
        (translatedConePivotEliminationForm b m A i₀)
        (indexedMatrixRowLinearPolynomial
          (translatedConeCoordinateSectionMatrix b m A) i) =
      MvPolynomial.C
          (m⁻¹ * translatedJoinVertexEvaluation A b m i) *
          translatedConePivotEliminationForm b m A i₀ +
        MvPolynomial.C m⁻¹ *
          indexedMatrixRowLinearPolynomial
            (projectiveSectionSpatialMatrix A) i := by
  classical
  unfold indexedMatrixRowLinearPolynomial
    translatedConeCoordinateSectionMatrix
  rw [Fintype.sum_option]
  simp only [optionLinearEliminationAlgHom_X_none,
    optionLinearEliminationAlgHom_X_some, map_add, map_mul, map_sum,
    optionLinearEliminationAlgHom_C]
  rw [translatedJoinVertexEvaluation_apply]
  unfold projectiveSectionSpatialMatrix
  simp only [← MvPolynomial.C_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_mul]
  ring

/-- The polynomial carried by a displayed eliminated row is its literal
alternating combination of the two spatial rows. -/
theorem indexedMatrixRowLinearPolynomial_translatedJoinImageThree
    (b : Fin 13 → ℚ) (m : ℚ)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4)
    (k : Fin 3) :
    indexedMatrixRowLinearPolynomial
        (translatedJoinImageThreeEquationMatrix A b m i₀) k =
      MvPolynomial.C (translatedJoinVertexEvaluation A b m i₀) *
          indexedMatrixRowLinearPolynomial (projectiveSectionSpatialMatrix A)
            (finThreeEquivNonpivotRow i₀ k) -
        MvPolynomial.C (translatedJoinVertexEvaluation A b m
            (finThreeEquivNonpivotRow i₀ k)) *
          indexedMatrixRowLinearPolynomial
            (projectiveSectionSpatialMatrix A) i₀ := by
  classical
  unfold indexedMatrixRowLinearPolynomial
    translatedJoinImageThreeEquationMatrix projectiveSectionSpatialMatrix
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_sub, map_mul, map_mul]
  ring

/-- The selected row vanishes after solving it for the distinguished
coordinate. -/
theorem optionLinearElimination_transformed_pivotRow
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4)
    (hpivot : translatedJoinVertexEvaluation A b m i₀ ≠ 0) :
    optionLinearEliminationAlgHom
        (translatedConePivotEliminationForm b m A i₀)
        (indexedMatrixRowLinearPolynomial
          (translatedConeCoordinateSectionMatrix b m A) i₀) = 0 := by
  rw [optionLinearElimination_transformedRow_apply b m hm A i₀ i₀]
  unfold translatedConePivotEliminationForm
  rw [map_mul]
  have hcancel :
      MvPolynomial.C (translatedJoinVertexEvaluation A b m i₀) *
          MvPolynomial.C (translatedJoinVertexEvaluation A b m i₀)⁻¹ =
        (1 : MvPolynomial (Fin 13) ℚ) := by
    rw [← map_mul, mul_inv_cancel₀ hpivot, map_one]
  calc
    MvPolynomial.C m⁻¹ *
          MvPolynomial.C (translatedJoinVertexEvaluation A b m i₀) *
          (-MvPolynomial.C
              (translatedJoinVertexEvaluation A b m i₀)⁻¹ *
            indexedMatrixRowLinearPolynomial
              (projectiveSectionSpatialMatrix A) i₀) +
        MvPolynomial.C m⁻¹ *
          indexedMatrixRowLinearPolynomial
            (projectiveSectionSpatialMatrix A) i₀ =
        MvPolynomial.C m⁻¹ *
          (-(MvPolynomial.C (translatedJoinVertexEvaluation A b m i₀) *
              MvPolynomial.C
                (translatedJoinVertexEvaluation A b m i₀)⁻¹) *
            indexedMatrixRowLinearPolynomial
              (projectiveSectionSpatialMatrix A) i₀ +
            indexedMatrixRowLinearPolynomial
              (projectiveSectionSpatialMatrix A) i₀) := by ring
    _ = 0 := by rw [hcancel]; ring

/-- Every remaining row becomes a fixed nonzero scalar multiple of the
corresponding displayed eliminated row. -/
theorem optionLinearElimination_transformed_nonpivotRow
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4)
    (hpivot : translatedJoinVertexEvaluation A b m i₀ ≠ 0)
    (k : Fin 3) :
    optionLinearEliminationAlgHom
        (translatedConePivotEliminationForm b m A i₀)
        (indexedMatrixRowLinearPolynomial
          (translatedConeCoordinateSectionMatrix b m A)
          (finThreeEquivNonpivotRow i₀ k)) =
      MvPolynomial.C
          (m⁻¹ * (translatedJoinVertexEvaluation A b m i₀)⁻¹) *
        indexedMatrixRowLinearPolynomial
          (translatedJoinImageThreeEquationMatrix A b m i₀) k := by
  rw [optionLinearElimination_transformedRow_apply b m hm A i₀
    (finThreeEquivNonpivotRow i₀ k)]
  rw [indexedMatrixRowLinearPolynomial_translatedJoinImageThree]
  unfold translatedConePivotEliminationForm
  rw [map_mul]
  rw [map_mul]
  have hcancel :
      MvPolynomial.C (translatedJoinVertexEvaluation A b m i₀) *
          MvPolynomial.C (translatedJoinVertexEvaluation A b m i₀)⁻¹ =
        (1 : MvPolynomial (Fin 13) ℚ) := by
    rw [← map_mul, mul_inv_cancel₀ hpivot, map_one]
  let R₀ := indexedMatrixRowLinearPolynomial
    (projectiveSectionSpatialMatrix A) i₀
  let i := (finThreeEquivNonpivotRow i₀ k : Fin 4)
  let R := indexedMatrixRowLinearPolynomial
    (projectiveSectionSpatialMatrix A) i
  let a : MvPolynomial (Fin 13) ℚ := MvPolynomial.C m⁻¹
  let c : MvPolynomial (Fin 13) ℚ :=
    MvPolynomial.C (translatedJoinVertexEvaluation A b m i₀)⁻¹
  let f : MvPolynomial (Fin 13) ℚ :=
    MvPolynomial.C (translatedJoinVertexEvaluation A b m i₀)
  let d : MvPolynomial (Fin 13) ℚ :=
    MvPolynomial.C (translatedJoinVertexEvaluation A b m i)
  have hcf : c * f = 1 := by
    simpa only [c, f, mul_comm] using hcancel
  change a * d * (-c * R₀) + a * R = a * c * (f * R - d * R₀)
  calc
    a * d * (-c * R₀) + a * R =
        a * c * (f * R - d * R₀) + a * (1 - c * f) * R := by ring
    _ = a * c * (f * R - d * R₀) := by rw [hcf]; ring

/-- Scheme-theoretic elimination of the four transformed rows gives
exactly the three displayed image rows. -/
theorem map_transformedRowIdeal_optionLinearElimination
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4)
    (hpivot : translatedJoinVertexEvaluation A b m i₀ ≠ 0) :
    (indexedMatrixRowLinearIdeal
        (translatedConeCoordinateSectionMatrix b m A)).map
        (optionLinearEliminationAlgHom
          (translatedConePivotEliminationForm b m A i₀)) =
      indexedMatrixRowLinearIdeal
        (translatedJoinImageThreeEquationMatrix A b m i₀) := by
  let l := translatedConePivotEliminationForm b m A i₀
  let e := optionLinearEliminationAlgHom l
  let B := translatedConeCoordinateSectionMatrix b m A
  let D := translatedJoinImageThreeEquationMatrix A b m i₀
  apply le_antisymm
  · rw [indexedMatrixRowLinearIdeal, Ideal.map_span]
    apply Ideal.span_le.2
    rintro f ⟨g, ⟨i, rfl⟩, rfl⟩
    by_cases hi : i = i₀
    · subst i
      rw [show e (indexedMatrixRowLinearPolynomial B i₀) = 0 by
        exact optionLinearElimination_transformed_pivotRow
          b m hm A i₀ hpivot]
      exact Ideal.zero_mem _
    · let k : Fin 3 := (finThreeEquivNonpivotRow i₀).symm ⟨i, hi⟩
      have hki : (finThreeEquivNonpivotRow i₀ k : Fin 4) = i := by
        exact congrArg Subtype.val
          ((finThreeEquivNonpivotRow i₀).apply_symm_apply ⟨i, hi⟩)
      have hrow : e (indexedMatrixRowLinearPolynomial B i) =
          MvPolynomial.C
              (m⁻¹ * (translatedJoinVertexEvaluation A b m i₀)⁻¹) *
            indexedMatrixRowLinearPolynomial D k := by
        simpa only [e, l, B, D, hki] using
          optionLinearElimination_transformed_nonpivotRow
            b m hm A i₀ hpivot k
      rw [hrow]
      exact (indexedMatrixRowLinearIdeal D).mul_mem_left _
        (Ideal.subset_span ⟨k, rfl⟩)
  · rw [indexedMatrixRowLinearIdeal]
    apply Ideal.span_le.2
    rintro f ⟨k, rfl⟩
    let i : Fin 4 := finThreeEquivNonpivotRow i₀ k
    have hrow : e (indexedMatrixRowLinearPolynomial B i) =
        MvPolynomial.C
            (m⁻¹ * (translatedJoinVertexEvaluation A b m i₀)⁻¹) *
          indexedMatrixRowLinearPolynomial D k := by
      exact optionLinearElimination_transformed_nonpivotRow
        b m hm A i₀ hpivot k
    have hsource : indexedMatrixRowLinearPolynomial B i ∈
        indexedMatrixRowLinearIdeal B :=
      Ideal.subset_span ⟨i, rfl⟩
    have hscaled :
        MvPolynomial.C
            (m⁻¹ * (translatedJoinVertexEvaluation A b m i₀)⁻¹) *
          indexedMatrixRowLinearPolynomial D k ∈
        (indexedMatrixRowLinearIdeal B).map e := by
      rw [← hrow]
      exact Ideal.mem_map_of_mem e hsource
    have hscalar :
        (m * translatedJoinVertexEvaluation A b m i₀) *
            (m⁻¹ * (translatedJoinVertexEvaluation A b m i₀)⁻¹) = 1 := by
      field_simp [hm, hpivot]
    have heq :
        MvPolynomial.C (m * translatedJoinVertexEvaluation A b m i₀) *
            (MvPolynomial.C
                (m⁻¹ * (translatedJoinVertexEvaluation A b m i₀)⁻¹) *
              indexedMatrixRowLinearPolynomial D k) =
          indexedMatrixRowLinearPolynomial D k := by
      rw [← mul_assoc, ← map_mul, hscalar, map_one, one_mul]
    rw [← heq]
    exact ((indexedMatrixRowLinearIdeal B).map e).mul_mem_left _ hscaled

/-- The transformed pivot row is a unit multiple of the kernel generator
of the substitution map. -/
theorem transformedPivotRow_eq_scalar_mul_kernelGenerator
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4)
    (hpivot : translatedJoinVertexEvaluation A b m i₀ ≠ 0) :
    indexedMatrixRowLinearPolynomial
        (translatedConeCoordinateSectionMatrix b m A) i₀ =
      MvPolynomial.C
          (m⁻¹ * translatedJoinVertexEvaluation A b m i₀) *
        (MvPolynomial.X none - MvPolynomial.rename some
          (translatedConePivotEliminationForm b m A i₀)) := by
  classical
  let β := translatedJoinVertexEvaluation A b m i₀
  let R := indexedMatrixRowLinearPolynomial
    (projectiveSectionSpatialMatrix A) i₀
  have hβ : β ≠ 0 := hpivot
  have hnone : translatedConeCoordinateSectionMatrix b m A i₀ none =
      m⁻¹ * β := by
    simp only [translatedConeCoordinateSectionMatrix, β]
    rw [translatedJoinVertexEvaluation_apply]
    rfl
  have hsome (j : Fin 13) :
      translatedConeCoordinateSectionMatrix b m A i₀ (some j) =
        m⁻¹ * projectiveSectionSpatialMatrix A i₀ j := by
    rfl
  have hrename : MvPolynomial.rename some R =
      ∑ j, MvPolynomial.C (projectiveSectionSpatialMatrix A i₀ j) *
        MvPolynomial.X (some j) := by
    unfold R indexedMatrixRowLinearPolynomial
    simp only [map_sum, map_mul, MvPolynomial.rename_C,
      MvPolynomial.rename_X]
  have hsum :
      (∑ j, MvPolynomial.C
          (m⁻¹ * projectiveSectionSpatialMatrix A i₀ j) *
            MvPolynomial.X (some j)) =
        MvPolynomial.C m⁻¹ * MvPolynomial.rename some R := by
    rw [hrename, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [map_mul]
    ring
  have hcancel :
      MvPolynomial.C (m⁻¹ * β) * MvPolynomial.C β⁻¹ =
        (MvPolynomial.C m⁻¹ : MvPolynomial (Option (Fin 13)) ℚ) := by
    rw [← map_mul]
    congr 1
    field_simp [hm, hβ]
  unfold indexedMatrixRowLinearPolynomial
  rw [Fintype.sum_option, hnone]
  simp_rw [hsome]
  rw [hsum]
  unfold translatedConePivotEliminationForm
  change MvPolynomial.C (m⁻¹ * β) * MvPolynomial.X none +
      MvPolynomial.C m⁻¹ * MvPolynomial.rename some R =
    MvPolynomial.C (m⁻¹ * β) *
      (MvPolynomial.X none - MvPolynomial.rename some
        (-MvPolynomial.C β⁻¹ * R))
  simp only [map_neg, map_mul, MvPolynomial.rename_C]
  have hcancel' :
      MvPolynomial.C m⁻¹ * MvPolynomial.C β * MvPolynomial.C β⁻¹ =
        (MvPolynomial.C m⁻¹ : MvPolynomial (Option (Fin 13)) ℚ) := by
    rw [← map_mul]
    exact hcancel
  calc
    MvPolynomial.C m⁻¹ * MvPolynomial.C β * MvPolynomial.X none +
        MvPolynomial.C m⁻¹ * MvPolynomial.rename some R =
      MvPolynomial.C m⁻¹ * MvPolynomial.C β * MvPolynomial.X none +
        (MvPolynomial.C m⁻¹ * MvPolynomial.C β * MvPolynomial.C β⁻¹) *
          MvPolynomial.rename some R := by rw [hcancel']
    _ = MvPolynomial.C m⁻¹ * MvPolynomial.C β *
        (MvPolynomial.X none -
          (-MvPolynomial.C β⁻¹ * MvPolynomial.rename some R)) := by ring

/-- Thus the kernel of the substitution map is already contained in the
four-row ideal. -/
theorem ker_optionLinearElimination_le_transformedRowIdeal
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4)
    (hpivot : translatedJoinVertexEvaluation A b m i₀ ≠ 0) :
    RingHom.ker (optionLinearEliminationAlgHom
        (translatedConePivotEliminationForm b m A i₀)) ≤
      indexedMatrixRowLinearIdeal
        (translatedConeCoordinateSectionMatrix b m A) := by
  rw [ker_optionLinearEliminationAlgHom]
  apply Ideal.span_le.2
  rintro f rfl
  let B := translatedConeCoordinateSectionMatrix b m A
  let l := translatedConePivotEliminationForm b m A i₀
  have hrow : indexedMatrixRowLinearPolynomial B i₀ =
      MvPolynomial.C
          (m⁻¹ * translatedJoinVertexEvaluation A b m i₀) *
        (MvPolynomial.X none - MvPolynomial.rename some l) := by
    exact transformedPivotRow_eq_scalar_mul_kernelGenerator
      b m hm A i₀ hpivot
  have hrowmem : indexedMatrixRowLinearPolynomial B i₀ ∈
      indexedMatrixRowLinearIdeal B :=
    Ideal.subset_span ⟨i₀, rfl⟩
  have hscaled :
      MvPolynomial.C
          (m⁻¹ * translatedJoinVertexEvaluation A b m i₀) *
        (MvPolynomial.X none - MvPolynomial.rename some l) ∈
      indexedMatrixRowLinearIdeal B := by
    rwa [← hrow]
  have hscalar :
      (m * (translatedJoinVertexEvaluation A b m i₀)⁻¹) *
          (m⁻¹ * translatedJoinVertexEvaluation A b m i₀) = 1 := by
    field_simp [hm, hpivot]
  have heq :
      MvPolynomial.C
          (m * (translatedJoinVertexEvaluation A b m i₀)⁻¹) *
          (MvPolynomial.C
              (m⁻¹ * translatedJoinVertexEvaluation A b m i₀) *
            (MvPolynomial.X none - MvPolynomial.rename some l)) =
        MvPolynomial.X none - MvPolynomial.rename some l := by
    rw [← mul_assoc, ← map_mul, hscalar, map_one, one_mul]
  rw [← heq]
  exact (indexedMatrixRowLinearIdeal B).mul_mem_left _ hscaled

/-- Elimination fixes every polynomial in the old cone variables, hence
maps the polynomial-extension cone ideal back to its base ideal. -/
theorem map_projectiveConeIdealExtension_optionLinearElimination
    (J : Ideal (MvPolynomial (Fin 13) ℚ))
    (l : MvPolynomial (Fin 13) ℚ) :
    (projectiveConeIdealExtension J).map
        (optionLinearEliminationAlgHom l) = J := by
  unfold projectiveConeIdealExtension
  have hcomp :
      (optionLinearEliminationAlgHom l).toRingHom.comp
          (MvPolynomial.rename some).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp
  calc
    (J.map (MvPolynomial.rename some)).map
        (optionLinearEliminationAlgHom l) =
      J.map ((optionLinearEliminationAlgHom l).toRingHom.comp
        (MvPolynomial.rename some).toRingHom) :=
      J.map_map (MvPolynomial.rename some).toRingHom
        (optionLinearEliminationAlgHom l).toRingHom
    _ = J.map (RingHom.id _) := by rw [hcomp]
    _ = J := Ideal.map_id J

/-- The complete coordinate-cone section maps to the complete displayed
three-row image section. -/
theorem map_coordinateConeSupRows_optionLinearElimination
    (J : Ideal (MvPolynomial (Fin 13) ℚ))
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4)
    (hpivot : translatedJoinVertexEvaluation A b m i₀ ≠ 0) :
    (projectiveConeIdealExtension J ⊔
        indexedMatrixRowLinearIdeal
          (translatedConeCoordinateSectionMatrix b m A)).map
        (optionLinearEliminationAlgHom
          (translatedConePivotEliminationForm b m A i₀)) =
      J ⊔ indexedMatrixRowLinearIdeal
        (translatedJoinImageThreeEquationMatrix A b m i₀) := by
  rw [Ideal.map_sup,
    map_projectiveConeIdealExtension_optionLinearElimination,
    map_transformedRowIdeal_optionLinearElimination b m hm A i₀ hpivot]

/-- Since the pivot row already generates the substitution kernel, the
complete source ideal is exactly the inverse image of the displayed target
ideal. -/
theorem coordinateConeSupRows_eq_comap_optionLinearElimination
    (J : Ideal (MvPolynomial (Fin 13) ℚ))
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4)
    (hpivot : translatedJoinVertexEvaluation A b m i₀ ≠ 0) :
    projectiveConeIdealExtension J ⊔
        indexedMatrixRowLinearIdeal
          (translatedConeCoordinateSectionMatrix b m A) =
      (J ⊔ indexedMatrixRowLinearIdeal
          (translatedJoinImageThreeEquationMatrix A b m i₀)).comap
        (optionLinearEliminationAlgHom
          (translatedConePivotEliminationForm b m A i₀)) := by
  let l := translatedConePivotEliminationForm b m A i₀
  let e := optionLinearEliminationAlgHom l
  let H := projectiveConeIdealExtension J ⊔
    indexedMatrixRowLinearIdeal
      (translatedConeCoordinateSectionMatrix b m A)
  let Q := J ⊔ indexedMatrixRowLinearIdeal
    (translatedJoinImageThreeEquationMatrix A b m i₀)
  have hmap : H.map e = Q := by
    exact map_coordinateConeSupRows_optionLinearElimination
      J b m hm A i₀ hpivot
  change H = Q.comap e
  rw [← hmap, Ideal.comap_map_of_surjective e
    (optionLinearEliminationAlgHom_surjective l)]
  rw [← RingHom.ker_eq_comap_bot]
  symm
  apply sup_eq_left.mpr
  exact (ker_optionLinearElimination_le_transformedRowIdeal
    b m hm A i₀ hpivot).trans le_sup_right

/-! ## The literal source-to-image quotient map -/

/-- The inverse homogeneous affine coordinate change also preserves
degree. -/
theorem isHomogeneous_homogeneousAffinePolynomialChange_symm
    {K : Type u} [Field K] {sigma : Type*}
    (b : sigma → K) (m : K) (hm : m ≠ 0)
    {f : MvPolynomial (Option sigma) K} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    ((homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm f).IsHomogeneous d := by
  let g : Option sigma → MvPolynomial (Option sigma) K := fun j ↦
    match j with
    | none => MvPolynomial.X none
    | some i => MvPolynomial.C m⁻¹ *
        (MvPolynomial.X (some i) -
          MvPolynomial.C (b i) * MvPolynomial.X none)
  change (MvPolynomial.aeval g f).IsHomogeneous d
  have hg : ∀ j, (g j).IsHomogeneous 1 := by
    intro j
    cases j with
    | none => exact MvPolynomial.isHomogeneous_X (R := K) none
    | some i =>
        exact ((MvPolynomial.isHomogeneous_X (R := K) (some i)).sub
          (MvPolynomial.isHomogeneous_C_mul_X (R := K) (b i) none)).C_mul _
  simpa using hf.aeval g hg

/-- Reindex the source and send the translated vertex to the distinguished
coordinate vertex. -/
def rankFourNonvertexSourceCoordinateAlgEquiv
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0) :
    MvPolynomial (Fin 14) ℚ ≃ₐ[ℚ]
      MvPolynomial (Option (Fin 13)) ℚ :=
  (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv 13)).trans
    (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm

/-- Pullback of image-coordinate polynomials to the source component,
followed by elimination of the distinguished coordinate. -/
def rankFourNonvertexProjectionQuotientAlgHom
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4) :
    MvPolynomial (Fin 14) ℚ →ₐ[ℚ] MvPolynomial (Fin 13) ℚ :=
  (optionLinearEliminationAlgHom
    (translatedConePivotEliminationForm b m A i₀)).comp
      (rankFourNonvertexSourceCoordinateAlgEquiv b m hm).toAlgHom

/-- A homogeneous section of the preceding quotient map. -/
def rankFourNonvertexProjectionQuotientSection
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0) :
    MvPolynomial (Fin 13) ℚ →ₐ[ℚ] MvPolynomial (Fin 14) ℚ :=
  (rankFourNonvertexSourceCoordinateAlgEquiv b m hm).symm.toAlgHom.comp
    (MvPolynomial.rename some)

theorem rankFourNonvertexProjectionQuotient_rightInverse
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4) :
    (rankFourNonvertexProjectionQuotientAlgHom b m hm A i₀).comp
        (rankFourNonvertexProjectionQuotientSection b m hm) =
      AlgHom.id ℚ _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [rankFourNonvertexProjectionQuotientAlgHom,
    rankFourNonvertexProjectionQuotientSection,
    rankFourNonvertexSourceCoordinateAlgEquiv]
  have hcancel : (MvPolynomial.C m : MvPolynomial (Fin 13) ℚ) *
      MvPolynomial.C m⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hm, map_one]
  rw [← mul_assoc, hcancel, one_mul]
  ring

theorem rankFourNonvertexProjectionQuotient_surjective
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4) :
    Function.Surjective
      (rankFourNonvertexProjectionQuotientAlgHom b m hm A i₀) := by
  intro f
  refine ⟨rankFourNonvertexProjectionQuotientSection b m hm f, ?_⟩
  have h := DFunLike.congr_fun
    (rankFourNonvertexProjectionQuotient_rightInverse b m hm A i₀) f
  exact h

theorem rankFourNonvertexProjectionQuotient_isHomogeneous
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) (i₀ : Fin 4)
    (d : ℕ) (f : MvPolynomial (Fin 14) ℚ)
    (hf : f.IsHomogeneous d) :
    (rankFourNonvertexProjectionQuotientAlgHom b m hm A i₀ f).IsHomogeneous d := by
  apply optionLinearEliminationAlgHom_isHomogeneous
    (translatedConePivotEliminationForm b m A i₀)
    (translatedConePivotEliminationForm_isHomogeneous b m A i₀)
  apply isHomogeneous_homogeneousAffinePolynomialChange_symm b m hm
  exact hf.rename_isHomogeneous

theorem rankFourNonvertexProjectionQuotientSection_isHomogeneous
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (d : ℕ) (f : MvPolynomial (Fin 13) ℚ)
    (hf : f.IsHomogeneous d) :
    (rankFourNonvertexProjectionQuotientSection b m hm f).IsHomogeneous d := by
  apply MvPolynomial.IsHomogeneous.rename_isHomogeneous
  apply isHomogeneous_homogeneousAffinePolynomialChange b m hm
  exact hf.rename_isHomogeneous

theorem finSuccReindexedMatrix_eq_reindexedHomogeneousEquationMatrix
    (A : Matrix (Fin 4) (Fin 14) ℚ) :
    finSuccReindexedMatrix A = reindexedHomogeneousEquationMatrix A := by
  rfl

/-- The complete literal source-section ideal, after the source coordinate
equivalence, is the coordinate cone cut by the transformed rows. -/
theorem map_rankSevenSourceSectionIdeal_nonvertexCoordinates
    (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℚ) :
    (rankSevenSourceSectionIdeal x₀ m hm equations A).map
        (rankFourNonvertexSourceCoordinateAlgEquiv
          (fun j ↦ (x₀ j : ℚ)) (m : ℚ) (by exact_mod_cast hm.ne')) =
      projectiveConeIdealExtension
          (finiteEquationIdeal (rationalizedEquationFinset equations)) ⊔
        indexedMatrixRowLinearIdeal
          (translatedConeCoordinateSectionMatrix
            (fun j ↦ (x₀ j : ℚ)) (m : ℚ)
              (reindexedHomogeneousEquationMatrix A)) := by
  let b : Fin 13 → ℚ := fun j ↦ (x₀ j : ℚ)
  let hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  let E := MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv 13)
  let T := homogeneousAffinePolynomialChangeAlgEquiv b (m : ℚ) hmQ
  let J := finiteEquationIdeal (rationalizedEquationFinset equations)
  let A' := finSuccReindexedMatrix A
  calc
    (rankSevenSourceSectionIdeal x₀ m hm equations A).map
        (rankFourNonvertexSourceCoordinateAlgEquiv b (m : ℚ) hmQ) =
      ((rankSevenSourceSectionIdeal x₀ m hm equations A).map E).map
        T.symm := by
          exact ((rankSevenSourceSectionIdeal x₀ m hm equations A).map_mapₐ
            E.toAlgHom T.symm.toAlgHom).symm
    _ = (translatedProjectiveConeIdeal b (m : ℚ) hmQ J ⊔
          indexedMatrixRowLinearIdeal A').map T.symm := by
      rw [map_rankSevenSourceSectionIdeal_finSuccRename]
    _ = projectiveConeIdealExtension J ⊔
          indexedMatrixRowLinearIdeal
            (translatedConeCoordinateSectionMatrix b (m : ℚ) A') := by
      exact map_translatedCone_sup_rows_homogeneousAffine_symm
        J b (m : ℚ) hmQ A'
    _ = projectiveConeIdealExtension J ⊔
          indexedMatrixRowLinearIdeal
            (translatedConeCoordinateSectionMatrix b (m : ℚ)
              (reindexedHomogeneousEquationMatrix A)) := by
      simp only [A',
        finSuccReindexedMatrix_eq_reindexedHomogeneousEquationMatrix]

/-- The source-section ideal is literally the inverse image of the
codimension-three rational image-section ideal under the split homogeneous
quotient map. -/
theorem rankSevenSourceSectionIdeal_eq_comap_nonvertexProjection
    (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℚ) (i₀ : Fin 4)
    (hpivot : Matrix.mulVec A (translatedJoinVertexFinVector
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ)) i₀ ≠ 0) :
    rankSevenSourceSectionIdeal x₀ m hm equations A =
      (finiteEquationIdeal (rationalizedEquationFinset equations) ⊔
          indexedMatrixRowLinearIdeal
            (translatedJoinImageThreeEquationMatrixFin A
              (fun j ↦ (x₀ j : ℚ)) (m : ℚ) i₀)).comap
        (rankFourNonvertexProjectionQuotientAlgHom
          (fun j ↦ (x₀ j : ℚ)) (m : ℚ) (by exact_mod_cast hm.ne')
          (reindexedHomogeneousEquationMatrix A) i₀) := by
  let b : Fin 13 → ℚ := fun j ↦ (x₀ j : ℚ)
  let hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  let U := rankFourNonvertexSourceCoordinateAlgEquiv b (m : ℚ) hmQ
  let A' := reindexedHomogeneousEquationMatrix A
  let l := translatedConePivotEliminationForm b (m : ℚ) A' i₀
  let e := optionLinearEliminationAlgHom l
  let J := finiteEquationIdeal (rationalizedEquationFinset equations)
  let D := translatedJoinImageThreeEquationMatrixFin A b (m : ℚ) i₀
  let H := projectiveConeIdealExtension J ⊔
    indexedMatrixRowLinearIdeal
      (translatedConeCoordinateSectionMatrix b (m : ℚ) A')
  have hpivot' : translatedJoinVertexEvaluation A' b (m : ℚ) i₀ ≠ 0 := by
    rw [translatedJoinVertexEvaluation_reindexed]
    exact hpivot
  have hsourceMap :
      (rankSevenSourceSectionIdeal x₀ m hm equations A).map U = H := by
    exact map_rankSevenSourceSectionIdeal_nonvertexCoordinates
      x₀ m hm equations A
  have hcoord : H =
      (J ⊔ indexedMatrixRowLinearIdeal D).comap e := by
    simpa only [H, J, D, e, l, A',
      translatedJoinImageThreeEquationMatrixFin] using
        coordinateConeSupRows_eq_comap_optionLinearElimination
          J b (m : ℚ) hmQ A' i₀ hpivot'
  calc
    rankSevenSourceSectionIdeal x₀ m hm equations A =
        ((rankSevenSourceSectionIdeal x₀ m hm equations A).map U).comap U :=
      (Ideal.comap_map_of_bijective U U.bijective).symm
    _ = ((J ⊔ indexedMatrixRowLinearIdeal D).comap e).comap U := by
      rw [hsourceMap, hcoord]
    _ = (J ⊔ indexedMatrixRowLinearIdeal D).comap
        (rankFourNonvertexProjectionQuotientAlgHom
          b (m : ℚ) hmQ A' i₀) := by
      rfl

/-- Minimal components and their complete projective Hilbert data pass
through the literal split quotient. -/
theorem exists_rationalNonvertexImageComponent
    (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (i₀ : Fin 4)
    (hI : I ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ m hm equations A))
    (hdegree : HasProjectiveDimensionDegree I 2 1)
    (hpivot : Matrix.mulVec A (translatedJoinVertexFinVector
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ)) i₀ ≠ 0) :
    ∃ Q : Ideal (MvPolynomial (Fin 13) ℚ),
      Q ∈ finiteMinimalPrimes
        (finiteEquationIdeal (rationalizedEquationFinset equations) ⊔
          indexedMatrixRowLinearIdeal
            (translatedJoinImageThreeEquationMatrixFin A
              (fun j ↦ (x₀ j : ℚ)) (m : ℚ) i₀)) ∧
      I = Q.comap (rankFourNonvertexProjectionQuotientAlgHom
        (fun j ↦ (x₀ j : ℚ)) (m : ℚ) (by exact_mod_cast hm.ne')
        (reindexedHomogeneousEquationMatrix A) i₀) ∧
      HasProjectiveDimensionDegree Q 2 1 := by
  let b : Fin 13 → ℚ := fun j ↦ (x₀ j : ℚ)
  let hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  let A' := reindexedHomogeneousEquationMatrix A
  let D := translatedJoinImageThreeEquationMatrixFin A b (m : ℚ) i₀
  let J := finiteEquationIdeal (rationalizedEquationFinset equations)
  let Q₀ := J ⊔ indexedMatrixRowLinearIdeal D
  let f := rankFourNonvertexProjectionQuotientAlgHom b (m : ℚ) hmQ A' i₀
  let g := rankFourNonvertexProjectionQuotientSection b (m : ℚ) hmQ
  have hsource : rankSevenSourceSectionIdeal x₀ m hm equations A =
      Q₀.comap f := by
    exact rankSevenSourceSectionIdeal_eq_comap_nonvertexProjection
      x₀ m hm equations A i₀ hpivot
  have hImin : I ∈ (Q₀.comap f).minimalPrimes := by
    rw [← hsource]
    exact (mem_finiteMinimalPrimes_iff _ _).mp hI
  have hfsurj : Function.Surjective f :=
    rankFourNonvertexProjectionQuotient_surjective
      b (m : ℚ) hmQ A' i₀
  change I ∈ (Q₀.comap f.toRingHom).minimalPrimes at hImin
  rw [Ideal.comap_minimalPrimes_eq_of_surjective hfsurj Q₀] at hImin
  obtain ⟨Q, hQmin, hIQ⟩ := hImin
  have hQdegree : HasProjectiveDimensionDegree Q 2 1 := by
    apply (hasProjectiveDimensionDegree_comap_surjective_iff
      (Ns := 13) (Nt := 12) f
      hfsurj
      g (rankFourNonvertexProjectionQuotient_rightInverse
        b (m : ℚ) hmQ A' i₀)
      (rankFourNonvertexProjectionQuotient_isHomogeneous
        b (m : ℚ) hmQ A' i₀)
      (rankFourNonvertexProjectionQuotientSection_isHomogeneous
        b (m : ℚ) hmQ) Q 2 1).mp
    change HasProjectiveDimensionDegree (Q.comap f.toRingHom) 2 1
    rw [hIQ]
    exact hdegree
  refine ⟨Q, ?_, ?_, hQdegree⟩
  · exact (mem_finiteMinimalPrimes_iff Q₀ Q).mpr hQmin
  · exact hIQ.symm

/-- Evaluation through the homogeneous section is evaluation at the
literal translated affine point. -/
theorem eval_rankFourNonvertexProjectionQuotientSection_affineChart
    (b : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (z : IntVector 13) (q : MvPolynomial (Fin 13) ℚ) :
    MvPolynomial.eval (fun i ↦ (integralAffineChartVector z i : ℚ))
        (rankFourNonvertexProjectionQuotientSection b m hm q) =
      MvPolynomial.eval (fun j ↦ b j + m * (z j : ℚ)) q := by
  unfold rankFourNonvertexProjectionQuotientSection
    rankFourNonvertexSourceCoordinateAlgEquiv
  change MvPolynomial.eval
      (fun i ↦ (integralAffineChartVector z i : ℚ))
      (MvPolynomial.rename (_root_.finSuccEquiv 13).symm
        (homogeneousAffinePolynomialChangeAlgEquiv b m hm
          (MvPolynomial.rename some q))) = _
  rw [MvPolynomial.eval_rename]
  change MvPolynomial.aeval
      ((fun i ↦ (integralAffineChartVector z i : ℚ)) ∘
        (_root_.finSuccEquiv 13).symm)
      (homogeneousAffinePolynomialChangeAlgEquiv b m hm
        (MvPolynomial.rename some q)) =
      MvPolynomial.aeval (fun j ↦ b j + m * (z j : ℚ)) q
  rw [aeval_homogeneousAffinePolynomialChange]
  rw [aeval_rename]
  congr 1
  apply MvPolynomial.algHom_ext
  intro j
  simp [homogeneousAffineLinearEquiv, integralAffineChartVector]

/-- A source-component affine-chart point therefore maps to a rational
zero of its rational image component. -/
theorem rationalNonvertexImageComponent_point
    (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (Q : Ideal (MvPolynomial (Fin 13) ℚ))
    (i₀ : Fin 4) (z : IntVector 13)
    (hIQ : I = Q.comap (rankFourNonvertexProjectionQuotientAlgHom
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ) (by exact_mod_cast hm.ne')
      (reindexedHomogeneousEquationMatrix A) i₀))
    (hzI : (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
      affineIdealZeroLocus I) :
    (fun j ↦ (integralAffineMap x₀ z m j : ℚ)) ∈
      affineIdealZeroLocus Q := by
  let b : Fin 13 → ℚ := fun j ↦ (x₀ j : ℚ)
  let hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  let A' := reindexedHomogeneousEquationMatrix A
  let f := rankFourNonvertexProjectionQuotientAlgHom b (m : ℚ) hmQ A' i₀
  let g := rankFourNonvertexProjectionQuotientSection b (m : ℚ) hmQ
  rw [mem_affineIdealZeroLocus_iff] at hzI ⊢
  intro q hq
  have hgq : g q ∈ I := by
    rw [hIQ]
    change f (g q) ∈ Q
    have hright := DFunLike.congr_fun
      (rankFourNonvertexProjectionQuotient_rightInverse
        b (m : ℚ) hmQ A' i₀) q
    have hfg : f (g q) = q := by
      simpa only [f, g, AlgHom.comp_apply, AlgHom.id_apply] using hright
    rw [hfg]
    exact hq
  have hzero := hzI (g q) hgq
  rw [eval_rankFourNonvertexProjectionQuotientSection_affineChart
    b (m : ℚ) hmQ z q] at hzero
  simpa [integralAffineMap, b] using hzero

/-- The range-generated and consecutive-coordinate presentations of a
matrix row ideal agree literally. -/
theorem indexedMatrixRowLinearIdeal_eq_matrixRowLinearIdeal
    {c N : ℕ} (D : Matrix (Fin c) (Fin N) ℚ) :
    indexedMatrixRowLinearIdeal D = matrixRowLinearIdeal D := by
  rfl

/-- The rational ideal occurring after elimination is exactly the rational
linear-section ideal used by the exceptional-locus definitions. -/
theorem rationalLinearSectionIdeal_eq_sup_indexedRows
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {c : ℕ} (D : Matrix (Fin c) (Fin 13) ℚ) :
    finiteEquationIdeal
        (rationalLinearSectionEquationFinset equations D) =
      finiteEquationIdeal (rationalizedEquationFinset equations) ⊔
        indexedMatrixRowLinearIdeal D := by
  rw [rationalLinearSectionEquationFinset,
    finiteEquationIdeal_union_rowLinearEquationFamily,
    finiteEquationIdeal_rationalMatrixRowLinearEquationFamily_eq,
    indexedMatrixRowLinearIdeal_eq_matrixRowLinearIdeal]

/-- A coefficient-extended rational minimal prime which remains prime is
an actual minimal prime of the coefficient-extended ambient ideal.  This is
the elementary faithful-flat minimality argument. -/
theorem qbarMap_mem_finiteMinimalPrimes_of_rationalMinimalPrime
    {N : ℕ}
    (J Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hQ : Q ∈ finiteMinimalPrimes J)
    (hQbarPrime :
      (Q.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime) :
    Q.map (MvPolynomial.map (algebraMap ℚ Qbar)) ∈
      finiteMinimalPrimes
        (J.map (MvPolynomial.map (algebraMap ℚ Qbar))) := by
  letI : Algebra (MvPolynomial (Fin (N + 1)) ℚ)
      (MvPolynomial (Fin (N + 1)) Qbar) :=
    MvPolynomial.algebraMvPolynomial
  let φ : MvPolynomial (Fin (N + 1)) ℚ →+*
      MvPolynomial (Fin (N + 1)) Qbar :=
    MvPolynomial.map (algebraMap ℚ Qbar)
  let QbarIdeal := Q.map φ
  have hQmin := (mem_finiteMinimalPrimes_iff J Q).mp hQ
  have hQbarOwn : QbarIdeal ∈ QbarIdeal.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton QbarIdeal
  apply (mem_finiteMinimalPrimes_iff _ _).mpr
  refine ⟨⟨hQbarPrime, Ideal.map_mono hQmin.1.2⟩, ?_⟩
  intro R hR hRQbar
  have hJRcomap : J ≤ R.comap φ := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hR.2
  have hcomapRQ : R.comap φ ≤ Q := by
    have hcomapMap : QbarIdeal.comap φ = Q := by
      simpa only [QbarIdeal, φ] using
        (Ideal.comap_map_eq_self_of_faithfullyFlat
          (B := MvPolynomial (Fin (N + 1)) Qbar) Q)
    rw [← hcomapMap]
    exact Ideal.comap_mono hRQbar
  have hQRcomap : Q ≤ R.comap φ :=
    hQmin.2 ⟨hR.1.comap φ, hJRcomap⟩ hcomapRQ
  have hQbarR : QbarIdeal ≤ R := by
    rw [Ideal.map_le_iff_le_comap]
    exact hQRcomap
  exact hQbarOwn.2 ⟨hR.1, hQbarR⟩ hRQbar

/-- Homogeneous vanishing of an integral representative gives vanishing
of the canonical representative of its projective class. -/
theorem projectivePointVanishes_of_integralAffineZero
    (P : Ideal (MvPolynomial (Fin 13) Qbar))
    (hP : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar))
    (x : IntVector 13) (hx : x ≠ 0)
    (hzero : (fun i ↦ algebraMap ℚ Qbar (x i : ℚ)) ∈
      affineIdealZeroLocus P) :
    ProjectivePointVanishesOnGeometricIdeal P
      (integralProjectiveClass x hx) := by
  let xrat : Fin 13 → ℚ := fun i ↦ (x i : ℚ)
  have hxrat : xrat ≠ 0 := intCast_ne_zero hx
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℚ xrat hxrat
  have ha' : a • xrat = (integralProjectiveClass x hx).rep := by
    simpa only [integralProjectiveClass, xrat] using ha
  have hscaled := smul_mem_affineIdealZeroLocus_of_isHomogeneous
    P hP hzero (algebraMap ℚ Qbar (a : ℚ))
  have hrep : (fun i ↦ algebraMap ℚ Qbar
      ((integralProjectiveClass x hx).rep i)) =
      fun i ↦ algebraMap ℚ Qbar (a : ℚ) *
        algebraMap ℚ Qbar (x i : ℚ) := by
    funext i
    have hi := congrFun ha' i
    change algebraMap ℚ Qbar
        ((integralProjectiveClass x hx).rep i) = _
    rw [← hi]
    change algebraMap ℚ Qbar ((a : ℚ) * (x i : ℚ)) = _
    exact map_mul (algebraMap ℚ Qbar) _ _
  rw [ProjectivePointVanishesOnGeometricIdeal, hrep]
  exact hscaled

namespace StandardAG

/-- The standard degree-one theorem: an integral projective variety of
degree one is a projective linear space over its ground field, and hence is
geometrically integral.  This is the sole geometric input retained by the
nonvertex projection proof; all projection, component, and Hilbert-function
transport is proved above. -/
def DegreeOneRationalProjectivePrimeIsGeometricallyPrime : Prop :=
  ∀ (N r : ℕ) (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    Q.IsPrime →
    Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    HasProjectiveDimensionDegree Q r 1 →
    (Q.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime

end StandardAG

/-! ## The actual nonvertex component projection -/

/-- The former application-specific nonvertex projection input follows
from the single classical degree-one theorem above.  All dependence on the
translated cone, the chosen pivot, the point, and the three displayed image
rows is handled by the literal elimination proved in this file. -/
theorem rankFourTranslatedConeNonvertexDegreeOneComponentProjection_internal
    (hgeometric :
      StandardAG.DegreeOneRationalProjectivePrimeIsGeometricallyPrime) :
    StandardAG.RankFourTranslatedConeNonvertexDegreeOneComponentProjection := by
  intro x₀ m hm equations A I z hhomogeneous _hArank hI hdegree hzI
    hx i₀ hpivot
  let b : Fin 13 → ℚ := fun j ↦ (x₀ j : ℚ)
  let hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  let D : Matrix (Fin 3) (Fin 13) ℚ :=
    translatedJoinImageThreeEquationMatrixFin A b (m : ℚ) i₀
  let J : Ideal (MvPolynomial (Fin 13) ℚ) :=
    finiteEquationIdeal (rationalizedEquationFinset equations)
  let Jsection : Ideal (MvPolynomial (Fin 13) ℚ) :=
    J ⊔ indexedMatrixRowLinearIdeal D
  obtain ⟨Q, hQminimal, hIQ, hQdegree⟩ :=
    exists_rationalNonvertexImageComponent
      x₀ m hm equations A I i₀ hI hdegree hpivot
  have hJhomogeneous : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) := by
    apply Ideal.homogeneous_span
    intro q hq
    rw [Finset.mem_coe, rationalizedEquationFinset,
      Finset.mem_image] at hq
    obtain ⟨f, hf, rfl⟩ := hq
    obtain ⟨e, he⟩ := hhomogeneous f hf
    exact ⟨e, he.map (Int.castRingHom ℚ)⟩
  have hJsectionHomogeneous : Jsection.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) :=
    hJhomogeneous.sup (indexedMatrixRowLinearIdeal_isHomogeneous D)
  have hQminimal' :=
    (mem_finiteMinimalPrimes_iff Jsection Q).mp (by
      simpa only [Jsection, J, D, b] using hQminimal)
  have hQprime : Q.IsPrime := hQminimal'.1.1
  have hQhomogeneous : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) :=
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
      hJsectionHomogeneous hQminimal'
  let QbarIdeal : Ideal (MvPolynomial (Fin 13) Qbar) :=
    Q.map (MvPolynomial.map (algebraMap ℚ Qbar))
  have hQbarPrime : QbarIdeal.IsPrime := by
    exact hgeometric 12 2 Q hQprime hQhomogeneous hQdegree
  have hQbarDegree : HasGeometricProjectiveDimensionDegree
      QbarIdeal 2 1 := by
    exact qbarHasProjectiveDimensionDegree_of_rational
      Q hQdegree hQbarPrime
  have hyQ : (fun j ↦ (integralAffineMap x₀ z m j : ℚ)) ∈
      affineIdealZeroLocus Q := by
    exact rationalNonvertexImageComponent_point
      x₀ m hm A I Q i₀ z hIQ hzI
  have hyQbar :
      (fun j ↦ algebraMap ℚ Qbar
        (integralAffineMap x₀ z m j : ℚ)) ∈
        affineIdealZeroLocus QbarIdeal := by
    exact (rational_zero_of_ideal_iff_qbar_zero_of_extension
      Q QbarIdeal rfl _).mp hyQ
  have hQbarHomogeneous : QbarIdeal.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar) :=
    isHomogeneous_map_mvPolynomialMap
      (algebraMap ℚ Qbar) Q hQhomogeneous
  have hyProjective : ProjectivePointVanishesOnGeometricIdeal QbarIdeal
      (integralProjectiveClass (integralAffineMap x₀ z m) hx) :=
    projectivePointVanishes_of_integralAffineZero
      QbarIdeal hQbarHomogeneous (integralAffineMap x₀ z m) hx hyQbar
  have hQbarMinimalMapped : QbarIdeal ∈ finiteMinimalPrimes
      (Jsection.map (MvPolynomial.map (algebraMap ℚ Qbar))) := by
    apply qbarMap_mem_finiteMinimalPrimes_of_rationalMinimalPrime
      Jsection Q
    · simpa only [Jsection, J, D, b] using hQminimal
    · exact hQbarPrime
  have hsectionEquality :
      finiteEquationIdeal
          (geometricLinearSectionEquationFinset equations D) =
        Jsection.map (MvPolynomial.map (algebraMap ℚ Qbar)) := by
    rw [geometricLinearSectionIdeal_eq_map_rationalLinearSectionIdeal,
      rationalLinearSectionIdeal_eq_sup_indexedRows]
  have hQbarGeometric : QbarIdeal ∈ finiteEquationMinimalPrimes
      (geometricLinearSectionEquationFinset equations D) := by
    rw [mem_finiteEquationMinimalPrimes_iff, hsectionEquality]
    exact (mem_finiteMinimalPrimes_iff _ _).mp hQbarMinimalMapped
  have hcomponent : IsProjectiveSectionComponent equations D QbarIdeal :=
    ⟨hQbarGeometric,
      geometricIrrelevantCoordinateIdeal_not_le_of_projectivePoint
        QbarIdeal _ hyProjective⟩
  exact ⟨QbarIdeal, by simpa only [D, b] using hcomponent,
    hyProjective, hQbarDegree⟩

end

end TranslatedDepthSeven
