import TranslatedDepthSeven.ProjectiveAffineChange
import TranslatedDepthSeven.HomogeneousCone
import TranslatedDepthSeven.GeometricPrimeness

/-!
# Transport of homogeneous projective zero loci

The homogeneous linear automorphism

`(s,z) ↦ (s, s y₀ + r z)`

has a literal pullback automorphism on the polynomial ring.  This file proves
the evaluation identity, preservation of homogeneity, and the resulting
transport theorem for projective hypersurfaces and finite common zero loci.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped LinearAlgebra.Projectivization

open MvPolynomial

universe u v

variable {K : Type u} {σ : Type v} [Field K]

/-- Pullback by `(s,z) ↦ (s,s y₀+r z)` on homogeneous coordinate
polynomials. -/
def homogeneousAffinePolynomialChangeHom (y₀ : σ → K) (r : K) :
    MvPolynomial (Option σ) K →ₐ[K] MvPolynomial (Option σ) K :=
  aeval fun j ↦
    match j with
    | none => X none
    | some i => C (y₀ i) * X none + C r * X (some i)

/-- Pullback by the inverse homogeneous linear map. -/
def homogeneousAffinePolynomialChangeInvHom (y₀ : σ → K) (r : K) :
    MvPolynomial (Option σ) K →ₐ[K] MvPolynomial (Option σ) K :=
  aeval fun j ↦
    match j with
    | none => X none
    | some i => C r⁻¹ * (X (some i) - C (y₀ i) * X none)

/-- The homogeneous pullback is a polynomial-ring automorphism when
`r ≠ 0`. -/
def homogeneousAffinePolynomialChangeAlgEquiv
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) :
    MvPolynomial (Option σ) K ≃ₐ[K] MvPolynomial (Option σ) K :=
  AlgEquiv.ofAlgHom (homogeneousAffinePolynomialChangeHom y₀ r)
    (homogeneousAffinePolynomialChangeInvHom y₀ r)
    (by
      ext j
      cases j with
      | none => simp [homogeneousAffinePolynomialChangeHom,
          homogeneousAffinePolynomialChangeInvHom]
      | some i =>
          simp [homogeneousAffinePolynomialChangeHom,
            homogeneousAffinePolynomialChangeInvHom, hr])
    (by
      ext j
      cases j with
      | none => simp [homogeneousAffinePolynomialChangeHom,
          homogeneousAffinePolynomialChangeInvHom]
      | some i =>
          simp [homogeneousAffinePolynomialChangeHom,
            homogeneousAffinePolynomialChangeInvHom, hr])

@[simp]
theorem homogeneousAffinePolynomialChangeAlgEquiv_X_none
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) :
    homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr (X none) = X none := by
  simp [homogeneousAffinePolynomialChangeAlgEquiv,
    homogeneousAffinePolynomialChangeHom]

@[simp]
theorem homogeneousAffinePolynomialChangeAlgEquiv_C
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) (a : K) :
    homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr (C a) = C a :=
  (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr).commutes a

@[simp]
theorem homogeneousAffinePolynomialChangeAlgEquiv_X_some
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) (i : σ) :
    homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr (X (some i)) =
      C (y₀ i) * X none + C r * X (some i) := by
  simp [homogeneousAffinePolynomialChangeAlgEquiv,
    homogeneousAffinePolynomialChangeHom]

/-- Evaluation after homogeneous pullback is evaluation at the displayed
homogeneous linear image. -/
theorem aeval_homogeneousAffinePolynomialChange
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (v : Option σ → K) (f : MvPolynomial (Option σ) K) :
    aeval v (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr f) =
      aeval (homogeneousAffineLinearEquiv y₀ r hr v) f := by
  change (aeval v).comp (homogeneousAffinePolynomialChangeHom y₀ r) f = _
  congr 1
  ext j
  cases j <;> simp [homogeneousAffinePolynomialChangeHom]

/-- Homogeneous degree is preserved by homogeneous affine pullback. -/
theorem isHomogeneous_homogeneousAffinePolynomialChange
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    {f : MvPolynomial (Option σ) K} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr f).IsHomogeneous d := by
  let g : Option σ → MvPolynomial (Option σ) K := fun j ↦
      match j with
      | none => X none
      | some i => C (y₀ i) * X none + C r * X (some i)
  change (aeval g f).IsHomogeneous d
  have hg : ∀ j, (g j).IsHomogeneous 1 := by
    intro j
    cases j with
    | none =>
        exact MvPolynomial.isHomogeneous_X (R := K) (none : Option σ)
    | some i =>
        exact
          (MvPolynomial.isHomogeneous_C_mul_X (R := K) (y₀ i)
            (none : Option σ)).add
          (MvPolynomial.isHomogeneous_C_mul_X (R := K) r (some i))
  simpa using hf.aeval g hg

/-- Mapping an ideal and pulling it back by the same homogeneous coordinate
automorphism recovers the ideal. -/
theorem homogeneousAffinePolynomialChange_comap_map
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial (Option σ) K)) :
    (I.map (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr)).comap
        (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr) = I :=
  Ideal.comap_map_of_bijective _
    (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr).bijective

/-- Prime ideals are preserved by the homogeneous coordinate
automorphism. -/
theorem homogeneousAffinePolynomialChange_map_isPrime
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial (Option σ) K)) [I.IsPrime] :
    (I.map (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr)).IsPrime := by
  infer_instance

/-- The induced equivalence of homogeneous-coordinate quotient algebras. -/
def homogeneousAffinePolynomialChangeQuotientAlgEquiv
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial (Option σ) K)) :
    (MvPolynomial (Option σ) K ⧸ I) ≃ₐ[K]
      MvPolynomial (Option σ) K ⧸
        I.map (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr) :=
  Ideal.quotientEquivAlg I _
    (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr) rfl

/-- The homogeneous coordinate rings before and after the projective
automorphism have the same Krull dimension. -/
theorem homogeneousAffinePolynomialChange_quotient_ringKrullDim_eq
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial (Option σ) K)) :
    ringKrullDim (MvPolynomial (Option σ) K ⧸ I) =
      ringKrullDim (MvPolynomial (Option σ) K ⧸
        I.map (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr)) :=
  ringKrullDim_eq_of_ringEquiv
    (homogeneousAffinePolynomialChangeQuotientAlgEquiv y₀ r hr I).toRingEquiv

variable {L : Type*} [Field L] [Algebra K L]

/-- Extension of coefficients commutes with the homogeneous coordinate
change. -/
theorem map_homogeneousAffinePolynomialChangeAlgEquiv
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (f : MvPolynomial (Option σ) K) :
    MvPolynomial.map (algebraMap K L)
        (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr f) =
      homogeneousAffinePolynomialChangeAlgEquiv
        (fun i ↦ algebraMap K L (y₀ i)) (algebraMap K L r)
        ((map_ne_zero (algebraMap K L)).2 hr)
        (MvPolynomial.map (algebraMap K L) f) := by
  let lhs : MvPolynomial (Option σ) K →+* MvPolynomial (Option σ) L :=
    (MvPolynomial.map (algebraMap K L)).comp
      (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr).toRingHom
  let rhs : MvPolynomial (Option σ) K →+* MvPolynomial (Option σ) L :=
    (homogeneousAffinePolynomialChangeAlgEquiv
      (fun i ↦ algebraMap K L (y₀ i)) (algebraMap K L r)
      ((map_ne_zero (algebraMap K L)).2 hr)).toRingHom.comp
        (MvPolynomial.map (algebraMap K L))
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, rhs]
    · intro j
      cases j with
      | none => simp [lhs, rhs]
      | some i => simp [lhs, rhs]
  change lhs f = rhs f
  exact RingHom.congr_fun hhom f

/-- Ideal extension commutes with the homogeneous coordinate change. -/
theorem map_map_homogeneousAffinePolynomialChangeAlgEquiv
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial (Option σ) K)) :
    (I.map (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr)).map
        (MvPolynomial.map (algebraMap K L)) =
      (I.map (MvPolynomial.map (algebraMap K L))).map
        (homogeneousAffinePolynomialChangeAlgEquiv
          (fun i ↦ algebraMap K L (y₀ i)) (algebraMap K L r)
          ((map_ne_zero (algebraMap K L)).2 hr)) := by
  change
    Ideal.map (MvPolynomial.map (algebraMap K L))
        (Ideal.map
          (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr).toRingHom I) =
      Ideal.map
        (homogeneousAffinePolynomialChangeAlgEquiv
          (fun i ↦ algebraMap K L (y₀ i)) (algebraMap K L r)
          ((map_ne_zero (algebraMap K L)).2 hr)).toRingHom
        (Ideal.map (MvPolynomial.map (algebraMap K L)) I)
  rw [Ideal.map_map, Ideal.map_map]
  apply congrArg (fun φ : MvPolynomial (Option σ) K →+*
      MvPolynomial (Option σ) L ↦ I.map φ)
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro j
    cases j <;> simp

/-- Geometric primeness of a homogeneous coordinate ideal is invariant
under the projective automorphism. -/
theorem geometricallyPrime_map_homogeneousAffinePolynomialChangeAlgEquiv_iff
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial (Option σ) K)) :
    GeometricallyPrimeMvPolynomialIdeal
        (I.map (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr)) ↔
      GeometricallyPrimeMvPolynomialIdeal I := by
  constructor
  · intro h E _ _
    let y₀' : σ → E := fun i ↦ algebraMap K E (y₀ i)
    let r' : E := algebraMap K E r
    have hr' : r' ≠ 0 := (map_ne_zero (algebraMap K E)).2 hr
    let φ : MvPolynomial (Option σ) E ≃+* MvPolynomial (Option σ) E :=
      (homogeneousAffinePolynomialChangeAlgEquiv y₀' r' hr').toRingEquiv
    have hbase :
        ((I.map (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr)).map
          (MvPolynomial.map (algebraMap K E))) =
          (I.map (MvPolynomial.map (algebraMap K E))).map φ := by
      simpa [y₀', r', φ] using
        (map_map_homogeneousAffinePolynomialChangeAlgEquiv
          (L := E) y₀ r hr I)
    have hprime :
        ((I.map (MvPolynomial.map (algebraMap K E))).map φ).IsPrime := by
      rw [← hbase]
      exact h E
    letI : ((I.map (MvPolynomial.map (algebraMap K E))).map φ).IsPrime := hprime
    have hback :
        (((I.map (MvPolynomial.map
          (algebraMap K E))).map φ).map φ.symm).IsPrime :=
      Ideal.map_isPrime_of_equiv φ.symm
    have hundo :
        ((I.map (MvPolynomial.map
          (algebraMap K E))).map φ).map φ.symm =
          I.map (MvPolynomial.map
            (algebraMap K E)) :=
      Ideal.map_of_equiv φ
    rw [hundo] at hback
    exact hback
  · intro h E _ _
    let y₀' : σ → E := fun i ↦ algebraMap K E (y₀ i)
    let r' : E := algebraMap K E r
    have hr' : r' ≠ 0 := (map_ne_zero (algebraMap K E)).2 hr
    let φ : MvPolynomial (Option σ) E ≃+* MvPolynomial (Option σ) E :=
      (homogeneousAffinePolynomialChangeAlgEquiv y₀' r' hr').toRingEquiv
    have hbase :
        ((I.map (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr)).map
          (MvPolynomial.map (algebraMap K E))) =
          (I.map (MvPolynomial.map (algebraMap K E))).map φ := by
      simpa [y₀', r', φ] using
        (map_map_homogeneousAffinePolynomialChangeAlgEquiv
          (L := E) y₀ r hr I)
    rw [hbase]
    letI : (I.map (MvPolynomial.map
        (algebraMap K E))).IsPrime := h E
    exact Ideal.map_isPrime_of_equiv φ

variable {L : Type*}

/-- The projective hypersurface cut out by one homogeneous polynomial,
defined through nonzero homogeneous representatives. -/
def homogeneousProjectiveHypersurface
    (f : MvPolynomial σ K) : Set (ℙ K (σ → K)) :=
  {P | ∃ (x : σ → K) (hx : x ≠ 0),
    P = Projectivization.mk K x hx ∧ aeval x f = 0}

/-- For a homogeneous polynomial, hypersurface membership can be checked on
any displayed nonzero representative. -/
theorem mk_mem_homogeneousProjectiveHypersurface_iff
    (f : MvPolynomial σ K) (d : ℕ) (hf : f.IsHomogeneous d)
    (x : σ → K) (hx : x ≠ 0) :
    Projectivization.mk K x hx ∈ homogeneousProjectiveHypersurface f ↔
      aeval x f = 0 := by
  constructor
  · rintro ⟨y, hy, hxy, hfy⟩
    change MvPolynomial.eval y f = 0 at hfy
    change MvPolynomial.eval x f = 0
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff' K x y hx hy).1 hxy
    have hscale := eval_smul_of_isHomogeneous f y a d hf
    rw [show (fun i ↦ a * y i) = x by simpa only [Pi.smul_apply, smul_eq_mul]
      using ha] at hscale
    rw [hscale, hfy, mul_zero]
  · intro hfx
    exact ⟨x, hx, rfl, hfx⟩

/-- The projective automorphism transports the hypersurface of `f` exactly
to the hypersurface of its homogeneous pullback. -/
theorem projectiveAffineMap_mem_homogeneousProjectiveHypersurface_iff
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (f : MvPolynomial (Option σ) K) (d : ℕ) (hf : f.IsHomogeneous d)
    (P : ℙ K (Option σ → K)) :
    projectiveAffineMap y₀ r hr P ∈ homogeneousProjectiveHypersurface f ↔
      P ∈ homogeneousProjectiveHypersurface
        (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr f) := by
  induction P using Projectivization.ind with
  | h v hv =>
      rw [projectiveAffineMap_mk]
      rw [mk_mem_homogeneousProjectiveHypersurface_iff f d hf]
      rw [mk_mem_homogeneousProjectiveHypersurface_iff _ d
        (isHomogeneous_homogeneousAffinePolynomialChange y₀ r hr hf)]
      rw [aeval_homogeneousAffinePolynomialChange]

/-- Because the projective automorphism fixes infinity pointwise, a
homogeneous hypersurface and its pullback have exactly the same points on the
hyperplane at infinity. -/
theorem projectiveAtInfinity_mem_homogeneousProjectiveHypersurface_change_iff
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (f : MvPolynomial (Option σ) K) (d : ℕ) (hf : f.IsHomogeneous d)
    (P : ℙ K (Option σ → K))
    (hP : P ∈ (projectiveHyperplaneAtInfinity :
      Set (ℙ K (Option σ → K)))) :
    P ∈ homogeneousProjectiveHypersurface f ↔
      P ∈ homogeneousProjectiveHypersurface
        (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr f) := by
  have hfix :=
    projectiveAffineMap_fixed_on_hyperplaneAtInfinity y₀ r hr hP
  simpa [hfix] using
    (projectiveAffineMap_mem_homogeneousProjectiveHypersurface_iff
      y₀ r hr f d hf P)

/-- The same transport identity for the common zero locus of a literal
finite family of homogeneous equations. -/
theorem projectiveAffineMap_mem_finiteCommonZeroLocus_iff
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (equations : Finset (MvPolynomial (Option σ) K))
    (degree : MvPolynomial (Option σ) K → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (P : ℙ K (Option σ → K)) :
    (∀ f ∈ equations,
        projectiveAffineMap y₀ r hr P ∈ homogeneousProjectiveHypersurface f) ↔
      (∀ f ∈ equations,
        P ∈ homogeneousProjectiveHypersurface
          (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr f)) := by
  apply forall_congr'
  intro f
  apply imp_congr_right
  intro hf
  exact projectiveAffineMap_mem_homogeneousProjectiveHypersurface_iff
    y₀ r hr f (degree f) (hhom f hf) P

/-- The corresponding equality on infinity for a finite homogeneous equation
family, equation by equation. -/
theorem projectiveAtInfinity_mem_finiteCommonZeroLocus_change_iff
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (equations : Finset (MvPolynomial (Option σ) K))
    (degree : MvPolynomial (Option σ) K → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (P : ℙ K (Option σ → K))
    (hP : P ∈ (projectiveHyperplaneAtInfinity :
      Set (ℙ K (Option σ → K)))) :
    (∀ f ∈ equations, P ∈ homogeneousProjectiveHypersurface f) ↔
      (∀ f ∈ equations,
        P ∈ homogeneousProjectiveHypersurface
          (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr f)) := by
  apply forall_congr'
  intro f
  apply imp_congr_right
  intro hf
  exact projectiveAtInfinity_mem_homogeneousProjectiveHypersurface_change_iff
    y₀ r hr f (degree f) (hhom f hf) P hP

end

end TranslatedDepthSeven
