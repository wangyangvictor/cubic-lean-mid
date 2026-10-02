import HessianTheorem11.BibleHyperplanes

/-!
# Literal incidence for singular hyperplane sections

This formalizes the incidence equations in the manuscript's section
“Bounds on terminal strata”: F(x)=0, v·x=0, and v_i F_j(x)-v_j F_i(x)=0.
For v nonzero they describe exactly the singular locus of the actual
polynomial restriction to the hyperplane, independently of its frame.
The finite polynomial equations also prove that the affine incidence is
algebraically closed. No dimension estimate, properness, semicontinuity,
or new algebraic-geometric input is assumed here.
-/

noncomputable section
namespace CubicTenVariables.TerminalSectionIncidence

open MvPolynomial HessianTheorem11 Matrix PolynomialRestriction

/-- The actual normal linear functional. -/
def normalFunctional {K : Type*} [CommRing K] {n : ℕ} (v : Fin n → K) :
    (Fin n → K) →ₗ[K] K where
  toFun x := dotProduct v x
  map_add' x y := dotProduct_add _ _ _
  map_smul' a x := by simp [dotProduct_smul, smul_eq_mul]

/-- The actual hyperplane subspace, also defined at the zero normal. -/
def hyperplane {K : Type*} [CommRing K] {n : ℕ} (v : Fin n → K) :
    Submodule K (Fin n → K) := LinearMap.ker (normalFunctional v)

@[simp] theorem mem_hyperplane {K : Type*} [CommRing K] {n : ℕ}
    (v x : Fin n → K) : x ∈ hyperplane v ↔ dotProduct v x = 0 := Iff.rfl

/-- All the displayed 2-by-2 minors of a normal and a differential. -/
def normalMinors {K : Type*} [CommRing K] {n : ℕ} (v g : Fin n → K) : Prop :=
  ∀ i j, v i * g j - v j * g i = 0

/-- For a nonzero normal, the literal minors say the differential is a
scalar multiple of that normal. -/
theorem minors_iff_mem_span {K : Type*} [Field K] {n : ℕ}
    (v g : Fin n → K) (hv : v ≠ 0) :
    normalMinors v g ↔ g ∈ Submodule.span K {v} := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra! hzero
      exact hv (funext hzero)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(v k)⁻¹ * g k, ?_⟩
    funext j
    have hj := sub_eq_zero.mp (h k j)
    change ((v k)⁻¹ * g k) * v j = g j
    calc
      ((v k)⁻¹ * g k) * v j = (v k)⁻¹ * (v j * g k) := by ring
      _ = (v k)⁻¹ * (v k * g j) := by rw [hj]
      _ = g j := by rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  · intro h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
    intro i j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- The annihilator of the normal's kernel is its actual one-dimensional
span. The proof uses explicit kernel vectors, not a dimension input. -/
theorem mem_span_iff_annihilator {K : Type*} [Field K] {n : ℕ}
    (v g : Fin n → K) (hv : v ≠ 0) :
    g ∈ Submodule.span K {v} ↔ ∀ y ∈ hyperplane v, dotProduct y g = 0 := by
  classical
  constructor
  · intro hg y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
    rw [dotProduct_smul, dotProduct_comm y v, (mem_hyperplane v y).mp hy]
    simp
  · intro h
    apply (minors_iff_mem_span v g hv).mp
    intro i j
    let y : Fin n → K :=
      v i • (Pi.single j 1 : Fin n → K) - v j • (Pi.single i 1 : Fin n → K)
    have hy : y ∈ hyperplane v := by
      change dotProduct v y = 0
      simp [y, dotProduct_sub, dotProduct_smul, smul_eq_mul, mul_comm]
    have hpair := h y hy
    simpa [y, sub_dotProduct, smul_dotProduct, smul_eq_mul] using hpair

theorem minors_iff_annihilator {K : Type*} [Field K] {n : ℕ}
    (v g : Fin n → K) (hv : v ≠ 0) :
    normalMinors v g ↔ ∀ y ∈ hyperplane v, dotProduct y g = 0 :=
  (minors_iff_mem_span v g hv).trans (mem_span_iff_annihilator v g hv)

/-- The actual affine hypersurface singular locus, retaining its equation
so the definition is correct without homogeneity or characteristic assumptions. -/
def hypersurfaceSingularLocus {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) : Set (Fin n → K) :=
  {x | eval x F = 0 ∧ gradient F x = 0}

/-- Actual affine incidence; the ordered pair is (point, normal). -/
def affineSectionSingularIncidence {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) : Set ((Fin n → K) × (Fin n → K)) :=
  {q | eval q.1 F = 0 ∧ dotProduct q.2 q.1 = 0 ∧ normalMinors q.2 (gradient F q.1)}

/-- The literal fiber at a normal vector. Its geometric interpretation below
requires that normal to be nonzero. -/
def sectionSingularFiber {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (v : Fin n → K) : Set (Fin n → K) :=
  {x | (x, v) ∈ affineSectionSingularIncidence F}

/-- The chain-rule/annihilator identity from BibleHyperplanes, over every
commutative coefficient ring rather than only the geometric field. -/
theorem gradient_restrict_zero_iff {K : Type*} [CommRing K] {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) K) (F : MvPolynomial (Fin n) K) (x : Fin m → K) :
    gradient (restrict B F) x = 0 ↔
      ∀ y : Fin m → K, dotProduct (B.mulVec y) (gradient F (B.mulVec x)) = 0 := by
  classical
  rw [BibleHyperplanes.gradient_restrict]
  have he (y : Fin m → K) :
      dotProduct (B.mulVec y) (gradient F (B.mulVec x)) =
        dotProduct y (B.transpose.mulVec (gradient F (B.mulVec x))) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp_rw [he]
  constructor
  · intro h y
    rw [h, dotProduct_zero]
  · intro h
    ext j
    simpa using h (Pi.single j 1)

/-- The fiber is intrinsically the zero hypersurface in the hyperplane
where the actual ambient differential annihilates that hyperplane. -/
theorem sectionSingularFiber_eq_annihilator {K : Type*} [Field K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (v : Fin n → K) (hv : v ≠ 0) :
    sectionSingularFiber F v =
      {x | eval x F = 0 ∧ x ∈ hyperplane v ∧
        ∀ y ∈ hyperplane v, dotProduct y (gradient F x) = 0} := by
  ext x
  simp only [sectionSingularFiber, affineSectionSingularIncidence, Set.mem_setOf_eq,
    mem_hyperplane, minors_iff_annihilator v _ hv]

/-- The actual restricted-polynomial singular locus maps exactly onto the
nonzero-normal incidence fiber. Only the range condition is needed; thus
this applies in particular to every injective frame spanning the hyperplane. -/
theorem frame_singular_image_eq_fiber {K : Type*} [Field K] {m n : ℕ}
    (F : MvPolynomial (Fin n) K) (v : Fin n → K) (hv : v ≠ 0)
    (B : Matrix (Fin n) (Fin m) K)
    (hRange : LinearMap.range B.mulVecLin = hyperplane v) :
    B.mulVec '' hypersurfaceSingularLocus (restrict B F) = sectionSingularFiber F v := by
  rw [sectionSingularFiber_eq_annihilator F v hv]
  ext x
  constructor
  · rintro ⟨u, ⟨hF, hg⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [eval_restrict] using hF
    · rw [← hRange]
      exact ⟨u, rfl⟩
    · intro y hy
      rw [← hRange] at hy
      obtain ⟨w, rfl⟩ := hy
      exact (gradient_restrict_zero_iff B F u).mp hg w
  · rintro ⟨hF, hx, hg⟩
    rw [← hRange] at hx
    obtain ⟨u, rfl⟩ := hx
    refine ⟨u, ⟨?_, ?_⟩, rfl⟩
    · simpa only [eval_restrict] using hF
    · apply (gradient_restrict_zero_iff B F u).mpr
      intro w
      apply hg
      rw [← hRange]
      exact ⟨w, rfl⟩

/-- Different actual frames of the same hyperplane give the identical
embedded singular locus, independently of their coordinate dimensions. -/
theorem frame_singular_image_independent {K : Type*} [Field K] {m k n : ℕ}
    (F : MvPolynomial (Fin n) K) (v : Fin n → K) (hv : v ≠ 0)
    (B : Matrix (Fin n) (Fin m) K) (C : Matrix (Fin n) (Fin k) K)
    (hB : LinearMap.range B.mulVecLin = hyperplane v)
    (hC : LinearMap.range C.mulVecLin = hyperplane v) :
    B.mulVec '' hypersurfaceSingularLocus (restrict B F) =
      C.mulVec '' hypersurfaceSingularLocus (restrict C F) := by
  rw [frame_singular_image_eq_fiber F v hv B hB,
    frame_singular_image_eq_fiber F v hv C hC]

/-- Euler's identity makes the cubic equation redundant on the normal
annihilator locus in characteristic zero. -/
theorem eval_cubic_zero_of_hyperplane_minors {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (v x : Fin n → K) (hv : v ≠ 0) (hx : x ∈ hyperplane v)
    (hm : normalMinors v (gradient F x)) : eval x F = 0 := by
  have hpair := (minors_iff_annihilator v (gradient F x) hv).mp hm x hx
  have he := euler_cubic hF x
  change dotProduct x (gradient F x) = 3 * eval x F at he
  rw [hpair] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

/-- The homogeneous cubic fiber is the intrinsic critical locus on the
hyperplane; the equation F=0 follows, rather than being silently omitted. -/
theorem cubic_sectionSingularFiber_eq_annihilator
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (v : Fin n → K) (hv : v ≠ 0) :
    sectionSingularFiber F v =
      {x | x ∈ hyperplane v ∧ ∀ y ∈ hyperplane v, dotProduct y (gradient F x) = 0} := by
  rw [sectionSingularFiber_eq_annihilator F v hv]
  ext x
  constructor
  · exact fun h => h.2
  · rintro ⟨hx, ha⟩
    exact ⟨eval_cubic_zero_of_hyperplane_minors F hF v x hv hx
      ((minors_iff_annihilator v (gradient F x) hv).mpr ha), hx, ha⟩

/-- Direct compatibility with the existing geometric singular-cone API. -/
theorem frame_singularCone_image_eq_fiber {m n : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (v : GeometricPoint n) (hv : v ≠ 0)
    (B : Matrix (Fin n) (Fin m) GeometricField)
    (hRange : LinearMap.range B.mulVecLin = hyperplane v) :
    B.mulVec '' BibleHyperplanes.singularCone (restrict B F) = sectionSingularFiber F v := by
  rw [BibleHyperplanes.frame_singular_image, hRange,
    cubic_sectionSingularFiber_eq_annihilator F hF v hv]

/-- Finite equation index: the cubic, the hyperplane equation, and all minors. -/
abbrev IncidenceEquationIndex (n : ℕ) := Option (Option (Fin n × Fin n))

/-- Literal incidence equations on the coordinate blocks x and v. -/
def incidenceEquation {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) :
    IncidenceEquationIndex n → MvPolynomial (Fin n ⊕ Fin n) K
  | none => rename Sum.inl F
  | some none => ∑ i, X (Sum.inr i) * X (Sum.inl i)
  | some (some (i, j)) =>
      X (Sum.inr i) * rename Sum.inl (pderiv j F) -
        X (Sum.inr j) * rename Sum.inl (pderiv i F)

/-- The finite equations are exactly the original incidence on the two
coordinate blocks, with no auxiliary variables or existential equations. -/
theorem incidence_iff_equations {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (z : (Fin n ⊕ Fin n) → K) :
    ((fun i => z (Sum.inl i)), (fun i => z (Sum.inr i))) ∈ affineSectionSingularIncidence F ↔
      ∀ e, eval z (incidenceEquation F e) = 0 := by
  constructor
  · rintro ⟨hF, hdot, hmin⟩ e
    rcases e with _ | (_ | ⟨i, j⟩)
    · simpa only [incidenceEquation, eval_rename, Function.comp_def] using hF
    · simpa only [incidenceEquation, map_sum, eval_mul, eval_X, dotProduct] using hdot
    · simpa only [incidenceEquation, eval_sub, eval_mul, eval_X, eval_rename,
        Function.comp_def, gradient] using hmin i j
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [incidenceEquation, eval_rename, Function.comp_def] using h none
    · simpa only [incidenceEquation, map_sum, eval_mul, eval_X, dotProduct] using h (some none)
    · intro i j
      simpa only [incidenceEquation, eval_sub, eval_mul, eval_X, eval_rename,
        Function.comp_def, gradient] using h (some (some (i, j)))

/-- The actual affine incidence is algebraically closed in the two
coordinate blocks, by its displayed finite polynomial equations. -/
theorem affineSectionSingularIncidence_closed {n : ℕ} (F : GeometricPolynomial n) :
    AlgebraicallyClosedSet
      {z : (Fin n ⊕ Fin n) → GeometricField |
        ((fun i => z (Sum.inl i)), (fun i => z (Sum.inr i))) ∈ affineSectionSingularIncidence F} := by
  have he :
      {z : (Fin n ⊕ Fin n) → GeometricField |
        ((fun i => z (Sum.inl i)), (fun i => z (Sum.inr i))) ∈ affineSectionSingularIncidence F} =
      zeroLocus GeometricField (Ideal.span (Set.range (incidenceEquation F))) := by
    ext z
    rw [zeroLocus_span]
    change (_ ∈ affineSectionSingularIncidence F) ↔ _
    rw [incidence_iff_equations]
    constructor
    · intro h P hP
      obtain ⟨e, rfl⟩ := hP
      exact h e
    · intro h e
      exact h (incidenceEquation F e) ⟨e, rfl⟩
  rw [he]
  exact algebraicallyClosedSet_zeroLocus _

end CubicTenVariables.TerminalSectionIncidence
