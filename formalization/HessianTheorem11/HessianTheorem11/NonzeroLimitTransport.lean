import HessianTheorem11.RationalDescent

/-! Actual zero-weight parts, special-linear orbits and rational boundary
exclusion. Textbook inputs are stated for every homogeneous degree. -/

noncomputable section
namespace HessianTheorem11.NonzeroLimitTransport
open MvPolynomial PolynomialRestriction PolynomialWeightTransport
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

/-- Keep precisely the occurring monomials of weight zero. -/
def zeroWeightPart (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) :
    MvPolynomial (Fin n) K :=
  Finsupp.filter (fun d => monomialWeight w d = 0) F

@[simp] theorem coeff_zeroWeightPart (F : MvPolynomial (Fin n) K)
    (w : Fin n → ℤ) (d : Fin n →₀ ℕ) :
    coeff d (zeroWeightPart F w) = if monomialWeight w d = 0 then coeff d F else 0 := rfl

@[simp] theorem support_zeroWeightPart (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) :
    (zeroWeightPart F w).support = F.support.filter (fun d => monomialWeight w d = 0) := rfl

theorem zeroWeightPart_homogeneous {d : ℕ} {F : MvPolynomial (Fin n) K}
    (hF : F.IsHomogeneous d) (w : Fin n → ℤ) : (zeroWeightPart F w).IsHomogeneous d := by
  intro e he
  have he' : coeff e F ≠ 0 := by
    intro hz
    apply he
    simp [hz]
  exact hF he'

theorem zeroWeightPart_weights (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) :
    ∀ d ∈ (zeroWeightPart F w).support, monomialWeight w d = 0 := by
  intro d hd
  exact (Finset.mem_filter.mp hd).2

theorem zeroWeightPart_ne_zero_of_not_positive (F : MvPolynomial (Fin n) K)
    (w : Fin n → ℤ) (hW : HasNonnegativeWeights F w)
    (hp : ¬ HasPositiveWeights F w) : zeroWeightPart F w ≠ 0 := by
  intro hz
  apply hp
  intro d hd
  have hw : monomialWeight w d ≠ 0 := by
    intro he
    have hc := congrArg (coeff d) hz
    apply Finsupp.mem_support_iff.mp hd
    simpa [he] using hc
  exact lt_of_le_of_ne (hW d hd) (Ne.symm hw)

/-- The explicit unipotent radical for vector weights `-w`. Off-diagonal
entries can only move a vector towards a strictly smaller variable weight. -/
def WeightUpperUnipotent (w : Fin n → ℤ) (U : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ i, U i i = 1) ∧ ∀ i j, i ≠ j → w j ≤ w i → U i j = 0

theorem WeightUpperUnipotent.fixes_minimum_column {w : Fin n → ℤ}
    {U : Matrix (Fin n) (Fin n) K} (hU : WeightUpperUnipotent w U)
    (j : Fin n) (hj : ∀ i, w j ≤ w i) : U.mulVec (Pi.single j 1) = Pi.single j 1 := by
  classical
  ext i
  rw [Matrix.mulVec_single_one]
  by_cases hij : i = j
  · subst j; simp [hU.1]
  · simp [Pi.single_apply, hij, hU.2 i j hij (hj i)]

/-- The whole highest vector-weight subspace is fixed pointwise. -/
theorem WeightUpperUnipotent.fixes_minimum_subspace {w : Fin n → ℤ}
    {U : Matrix (Fin n) (Fin n) K} (hU : WeightUpperUnipotent w U)
    (v : Fin n → K) (hv : ∀ j, v j ≠ 0 → ∀ i, w j ≤ w i) : U.mulVec v = v := by
  classical
  have he : v = ∑ j, v j • (Pi.single j (1 : K) : Fin n → K) := by
    ext i
    simp [Pi.single_apply]
  rw [he, Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : v j = 0
  · simp [hj]
  · rw [Matrix.mulVec_smul, hU.fixes_minimum_column j (hv j hj)]

/-- The actual special-linear coordinate orbit. Inverting all matrices turns
this right substitution convention into the usual action `g.F=F(g⁻¹x)`. -/
def slOrbit (F : MvPolynomial (Fin n) K) : Set (MvPolynomial (Fin n) K) :=
  {G | ∃ B : Matrix (Fin n) (Fin n) K, B.det = 1 ∧ G = restrict B F}

/-- Polynomial-function Zariski closure in coefficient coordinates. Each test
polynomial depends on finitely many coefficients; on a bounded-degree space
this is exactly its usual finite-dimensional affine Zariski closure. -/
def slOrbitClosure (F : MvPolynomial (Fin n) K) : Set (MvPolynomial (Fin n) K) :=
  {G | ∀ P : MvPolynomial (Fin n →₀ ℕ) K,
    (∀ H ∈ slOrbit F, eval (fun d => coeff d H) P = 0) →
      eval (fun d => coeff d G) P = 0}

def ClosedSLOrbit (F : MvPolynomial (Fin n) K) : Prop := slOrbitClosure F ⊆ slOrbit F

theorem slOrbit_subset_closure (F : MvPolynomial (Fin n) K) :
    slOrbit F ⊆ slOrbitClosure F := by
  intro G hG P hP
  exact hP G hG

theorem self_mem_slOrbit (F : MvPolynomial (Fin n) K) : F ∈ slOrbit F := by
  refine ⟨1, Matrix.det_one, ?_⟩
  simp

/-- Rational relative-boundary Hilbert--Mumford/Kempf, specialized only to
the standard representation on forms. It is universal in degree and form;
its rationality assertion uses the perfect field ℚ and a rational point.
No anisotropy, cubic, Hessian, or numerical inequality occurs in this input. -/
structure RationalRelativeBoundaryInput : Prop where
  boundary : ∀ {n d : ℕ} (F : RationalPolynomial n),
    0 < d → F.IsHomogeneous d → F ≠ 0 →
    ¬ ClosedSLOrbit (geometricPolynomial F) →
    ∃ B : Matrix (Fin n) (Fin n) ℚ, Function.Injective B.mulVec ∧
      ∃ w : Fin n → ℤ, (∑ i, w i) = 0 ∧ w ≠ 0 ∧
        HasNonnegativeWeights (restrict B F) w

/-- Anisotropy excludes every nontrivial rational existing diagonal limit,
including limits with nonzero weight-zero part. -/
theorem rational_existing_limit_trivial (F : AnisotropicCubic n)
    (B : Matrix (Fin n) (Fin n) ℚ) (hB : Function.Injective B.mulVec)
    (w : Fin n → ℤ) (hsum : ∑ i, w i = 0)
    (hW : HasNonnegativeWeights (restrict B F.polynomial) w) : w = 0 :=
  rational_zero_sum_admissible_weights_trivial (restrictedCubic B F hB) w hW hsum

/-- The actual geometric special-linear orbit is closed. -/
theorem anisotropic_closedSLOrbit (boundary : RationalRelativeBoundaryInput)
    (F : AnisotropicCubic n) (hn : 0 < n) :
    ClosedSLOrbit (geometricPolynomial F.polynomial) := by
  by_contra hclosed
  obtain ⟨B, hB, w, hsum, hw, hW⟩ := boundary.boundary F.polynomial
    (by decide : 0 < 3) F.homogeneous (anisotropic_polynomial_ne_zero hn F) hclosed
  exact hw (rational_existing_limit_trivial F B hB w hsum hW)

theorem lowerBound_add {P Q : MvPolynomial (Fin n) K} {w : Fin n → ℤ} {a : ℤ}
    (hP : HasWeightLowerBound P w a) (hQ : HasWeightLowerBound Q w a) :
    HasWeightLowerBound (P + Q) w a := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hP d h
  · exact hQ d h

theorem lowerBound_mono {P : MvPolynomial (Fin n) K} {w : Fin n → ℤ} {a b : ℤ}
    (hP : HasWeightLowerBound P w a) (h : b ≤ a) : HasWeightLowerBound P w b :=
  fun d hd => h.trans (hP d hd)

/-- Two polynomials have the same first weight component, with a strict
one-step bound on their difference. -/
def SameLeading (w : Fin n → ℤ) (a : ℤ) (P Q : MvPolynomial (Fin n) K) : Prop :=
  HasWeightLowerBound P w a ∧ HasWeightLowerBound Q w a ∧
    HasWeightLowerBound (P-Q) w (a+1)

theorem SameLeading.mul {w : Fin n → ℤ} {a b : ℤ}
    {P P' Q Q' : MvPolynomial (Fin n) K}
    (hP : SameLeading w a P P') (hQ : SameLeading w b Q Q') :
    SameLeading w (a+b) (P*Q) (P'*Q') := by
  refine ⟨lowerBound_mul w hP.1 hQ.1, lowerBound_mul w hP.2.1 hQ.2.1, ?_⟩
  have he : P*Q-P'*Q' = (P-P')*Q + P'*(Q-Q') := by ring
  rw [he]
  apply lowerBound_add
  · convert lowerBound_mul w hP.2.2 hQ.1 using 1 <;> ring
  · convert lowerBound_mul w hP.2.1 hQ.2.2 using 1 <;> ring

theorem SameLeading.C (w : Fin n → ℤ) (c : K) : SameLeading w 0 (C c) (C c) := by
  refine ⟨lowerBound_C w c, lowerBound_C w c, ?_⟩
  simpa using lowerBound_zero (K := K) w 1

theorem SameLeading.pow {w : Fin n → ℤ} {a : ℤ}
    {P Q : MvPolynomial (Fin n) K} (h : SameLeading w a P Q) (k : ℕ) :
    SameLeading w ((k:ℤ)*a) (P^k) (Q^k) := by
  induction k with
  | zero => simpa using SameLeading.C w (1:K)
  | succ k ih => simpa [pow_succ, Nat.cast_add, add_mul] using ih.mul h

theorem SameLeading.prod {ι : Type*} {w : Fin n → ℤ}
    (s : Finset ι) (a : ι → ℤ) (P Q : ι → MvPolynomial (Fin n) K)
    (h : ∀ i ∈ s, SameLeading w (a i) (P i) (Q i)) :
    SameLeading w (∑ i ∈ s, a i) (∏ i ∈ s, P i) (∏ i ∈ s, Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SameLeading.C w (1:K)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem WeightUpperUnipotent.entry_monotone {w : Fin n → ℤ}
    {U : Matrix (Fin n) (Fin n) K} (hU : WeightUpperUnipotent w U)
    (i j : Fin n) (hij : U i j ≠ 0) : w i ≤ w j := by
  by_contra hn
  have hne : i ≠ j := by rintro rfl; omega
  exact hij (hU.2 i j hne (by omega))

theorem WeightUpperUnipotent.linearForms_leading {w : Fin n → ℤ}
    {U : Matrix (Fin n) (Fin n) K} (hU : WeightUpperUnipotent w U) (i : Fin n) :
    SameLeading w (w i) (linearForms U i) (X i) := by
  classical
  refine ⟨lowerBound_linearForms U w w hU.entry_monotone i, ?_, ?_⟩
  · simpa [X, monomialWeight_single] using
      lowerBound_monomial (K := K) w (Finsupp.single i 1) (1:K)
        (by simp [monomialWeight_single] : w i ≤ monomialWeight w (Finsupp.single i 1))
  · have he : linearForms U i - X i = linearForms (U-1) i := by
      simp [linearForms, Matrix.sub_apply, Matrix.one_apply, map_sub,
        sub_mul, Finset.sum_sub_distrib]
    rw [he]
    apply lowerBound_sum
    intro j _
    by_cases hz : (U-1) i j = 0
    · simpa [hz] using lowerBound_zero (K := K) w (w i+1)
    · have hne : i ≠ j := by
        rintro rfl
        simp [Matrix.sub_apply, hU.1] at hz
      have hu : U i j ≠ 0 := by simpa [Matrix.sub_apply, Matrix.one_apply, hne] using hz
      have hlt : w i < w j := by
        by_contra hn
        exact hu (hU.2 i j hne (by omega))
      have hterm : C ((U-1) i j) * X j =
          monomial (Finsupp.single j 1) ((U-1) i j) := by
        simp only [C_apply, X, monomial_mul, zero_add, mul_one]
      rw [hterm]
      apply lowerBound_monomial
      simpa [monomialWeight_single] using (show w i+1 ≤ w j by omega)

theorem WeightUpperUnipotent.monomial_leading {w : Fin n → ℤ}
    {U : Matrix (Fin n) (Fin n) K} (hU : WeightUpperUnipotent w U)
    (d : Fin n →₀ ℕ) (c : K) :
    SameLeading w (monomialWeight w d) (restrict U (monomial d c)) (monomial d c) := by
  classical
  have hp := SameLeading.prod d.support (fun i => (d i:ℤ)*w i)
    (fun i => linearForms U i ^d i) (fun i => X i ^d i)
    (fun i _ => (hU.linearForms_leading i).pow (d i))
  have hs : (∑ i ∈ d.support, (d i:ℤ)*w i) = monomialWeight w d := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]
  rw [hs] at hp
  have hm := (SameLeading.C w c).mul hp
  simpa only [restrict, zero_add, monomial_eq, Finsupp.prod,
    map_mul, map_prod, map_pow, aeval_C, aeval_X] using hm

theorem WeightUpperUnipotent.difference_positive {w : Fin n → ℤ}
    {U : Matrix (Fin n) (Fin n) K} (hU : WeightUpperUnipotent w U)
    (F : MvPolynomial (Fin n) K) (hF : HasNonnegativeWeights F w) :
    HasPositiveWeights (restrict U F-F) w := by
  classical
  have he : restrict U F-F = ∑ d ∈ F.support,
      (restrict U (monomial d (coeff d F))-monomial d (coeff d F)) := by
    conv_lhs => rw [F.as_sum]
    simp only [restrict, map_sum, Finset.sum_sub_distrib]
  have hb : HasWeightLowerBound (restrict U F-F) w 1 := by
    rw [he]
    apply lowerBound_sum
    intro d hd
    exact lowerBound_mono (hU.monomial_leading d (coeff d F)).2.2 (by have := hF d hd; omega)
  intro d hd
  have := hb d hd
  omega

theorem WeightUpperUnipotent.zeroWeightPart_restrict {w : Fin n → ℤ}
    {U : Matrix (Fin n) (Fin n) K} (hU : WeightUpperUnipotent w U)
    (F : MvPolynomial (Fin n) K) (hF : HasNonnegativeWeights F w) :
    zeroWeightPart (restrict U F) w = zeroWeightPart F w := by
  have hp := hU.difference_positive F hF
  ext d
  simp only [coeff_zeroWeightPart]
  split_ifs with hd
  · have hz : coeff d (restrict U F-F) = 0 := by
      by_contra hn
      have hh := hp d (Finsupp.mem_support_iff.mpr hn)
      omega
    change coeff d (restrict U F) - coeff d F = 0 at hz
    exact sub_eq_zero.mp hz
  · rfl

/-- Opposite parabolic matrices lower the weights of polynomial monomials. -/
def WeightLowerTriangular (w : Fin n → ℤ) (P : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j, P i j ≠ 0 → w j ≤ w i

theorem monomialWeight_neg (w : Fin n → ℤ) (d : Fin n →₀ ℕ) :
    monomialWeight (-w) d = -monomialWeight w d := by
  simp [monomialWeight, Finset.sum_neg_distrib]

theorem WeightLowerTriangular.restrict_zeroWeightPart_nonpositive {w : Fin n → ℤ}
    {P : Matrix (Fin n) (Fin n) K} (hP : WeightLowerTriangular w P)
    (F : MvPolynomial (Fin n) K) :
    ∀ d ∈ (restrict P (zeroWeightPart F w)).support, monomialWeight w d ≤ 0 := by
  have hn : HasNonnegativeWeights (zeroWeightPart F w) (-w) := by
    intro d hd
    rw [monomialWeight_neg, zeroWeightPart_weights F w d hd]
    omega
  have hentries : ∀ i j, P i j ≠ 0 → (-w) i ≤ (-w) j := by
    intro i j hij
    have := hP i j hij
    simp only [Pi.neg_apply]
    omega
  have ht := hasNonnegativeWeights_restrict_of_entry_weights P (-w) (-w)
    hentries (zeroWeightPart F w) hn
  intro d hd
  have := ht d hd
  rw [monomialWeight_neg] at this
  omega

theorem zeroWeightPart_eq_self_of_weight_zero (F : MvPolynomial (Fin n) K)
    (w : Fin n → ℤ) (hF : ∀ d ∈ F.support, monomialWeight w d = 0) :
    zeroWeightPart F w = F := by
  ext d
  rw [coeff_zeroWeightPart]
  split_ifs with hd
  · rfl
  · have hc : coeff d F = 0 := by
      by_contra hc
      exact hd (hF d (Finsupp.mem_support_iff.mpr hc))
    exact hc.symm

/-- The elementary polynomial half of the source's block-unitriangular
transport proof. The big-cell factors are actual matrices; the conclusion
is derived from strict support bounds on their substitution actions. -/
theorem transport_of_big_cell_decomposition
    (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) (hF : HasNonnegativeWeights F w)
    (U V P : Matrix (Fin n) (Fin n) K)
    (hUV : U*V=1) (hV : WeightUpperUnipotent w V) (hP : WeightLowerTriangular w P)
    (hdecomp : F = restrict U (restrict P (zeroWeightPart F w))) :
    zeroWeightPart F w = restrict V F := by
  have heq : restrict V F = restrict P (zeroWeightPart F w) := by
    calc
      restrict V F = restrict V (restrict U (restrict P (zeroWeightPart F w))) :=
        congrArg (restrict V) hdecomp
      _ = restrict P (zeroWeightPart F w) := by rw [restrict_restrict, hUV, restrict_one]
  have hn := hasNonnegativeWeights_restrict_of_entry_weights V w w hV.entry_monotone F hF
  have hz : ∀ d ∈ (restrict V F).support, monomialWeight w d = 0 := by
    intro d hd
    have hp := hP.restrict_zeroWeightPart_nonpositive F d (heq ▸ hd)
    have hp' := hn d hd
    omega
  rw [← hV.zeroWeightPart_restrict F hF, zeroWeightPart_eq_self_of_weight_zero _ _ hz]

/-- The standard open-orbit-map and opposite-big-cell consequence, stated
for homogeneous forms of arbitrary degree. `decompose` is the big-cell
factorization of a point on an existing diagonal curve in a closed orbit.
It does not assert unipotent transport: that is proved above from actual
polynomial support. See NONZERO_LIMIT_INPUT_AUDIT.md for the geometric
argument and the separate role of rational boundary descent. -/
structure TextbookOrbitBigCellInput : Prop where
  decompose : ∀ {n d : ℕ} (F : GeometricPolynomial n), F.IsHomogeneous d →
    ClosedSLOrbit F → ∀ B : Matrix (Fin n) (Fin n) GeometricField,
    Function.Injective B.mulVec → ∀ w : Fin n → ℤ, (∑ i, w i)=0 →
    HasNonnegativeWeights (restrict B F) w →
    ∃ U V P : Matrix (Fin n) (Fin n) GeometricField,
      U*V=1 ∧ V.det=1 ∧ WeightUpperUnipotent w U ∧ WeightUpperUnipotent w V ∧
      WeightLowerTriangular w P ∧
      restrict B F = restrict U (restrict P (zeroWeightPart (restrict B F) w))

/-- Every existing zero-weight limit of an anisotropic rational cubic is
obtained by an actual unipotent substitution fixing its minimum-weight
coordinate subspace pointwise. -/
theorem anisotropic_zeroWeightPart_transport
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic n) (hn : 0<n)
    (B : Matrix (Fin n) (Fin n) GeometricField) (hB : Function.Injective B.mulVec)
    (w : Fin n → ℤ) (hsum : ∑ i, w i=0)
    (hW : HasNonnegativeWeights (restrict B (geometricPolynomial F.polynomial)) w) :
    ∃ U : Matrix (Fin n) (Fin n) GeometricField,
      U.det=1 ∧ WeightUpperUnipotent w U ∧
      zeroWeightPart (restrict B (geometricPolynomial F.polynomial)) w =
        restrict U (restrict B (geometricPolynomial F.polynomial)) := by
  obtain ⟨U,V,P,hUV,hVdet,hU,hV,hP,hdecomp⟩ := bigCell.decompose
    (geometricPolynomial F.polynomial) (geometric_homogeneous F.homogeneous)
    (anisotropic_closedSLOrbit boundary F hn) B hB w hsum hW
  exact ⟨V,hVdet,hV,transport_of_big_cell_decomposition _ w hW U V P hUV hV hP hdecomp⟩

theorem restrict_ne_zero (F : MvPolynomial (Fin n) K) (hF : F ≠ 0)
    (B : Matrix (Fin n) (Fin n) K) (hB : Function.Injective B.mulVec) :
    restrict B F ≠ 0 := by
  intro hz
  apply hF
  have hh : restrict (frameTransition B 1 hB) (restrict B F) = 0 := by
    rw [hz]
    exact map_zero (aeval (linearForms (frameTransition B 1 hB)))
  rw [restrict_restrict, matrix_mul_frameTransition, restrict_one] at hh
  exact hh

theorem injective_of_det_one (B : Matrix (Fin n) (Fin n) K) (hB : B.det=1) :
    Function.Injective B.mulVec := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det B).mpr
  rw [hB]
  exact isUnit_one

/-- The transported weight-zero polynomial is nonzero. -/
theorem anisotropic_zeroWeightPart_ne_zero
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic n) (hn : 0<n)
    (B : Matrix (Fin n) (Fin n) GeometricField) (hB : Function.Injective B.mulVec)
    (w : Fin n → ℤ) (hsum : ∑ i, w i=0)
    (hW : HasNonnegativeWeights (restrict B (geometricPolynomial F.polynomial)) w) :
    zeroWeightPart (restrict B (geometricPolynomial F.polynomial)) w ≠ 0 := by
  obtain ⟨U,hU,htri,heq⟩ := anisotropic_zeroWeightPart_transport
    boundary bigCell F hn B hB w hsum hW
  rw [heq]
  exact restrict_ne_zero _
    (restrict_ne_zero _ (RationalDescent.geometricPolynomial_ne_zero _
      (anisotropic_polynomial_ne_zero hn F)) B hB) U (injective_of_det_one U hU)

end HessianTheorem11.NonzeroLimitTransport
