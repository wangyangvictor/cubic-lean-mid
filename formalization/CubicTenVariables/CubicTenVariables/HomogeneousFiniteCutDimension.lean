import HessianTheorem11.UnconditionalCutDimension
import TranslatedDepthSeven.PrimeAffineNoetherNormalization
import CubicTenVariables.HomogeneousPowerCertificates

/-! Dimension bounds from finitely many positive homogeneous cuts. The cut
estimate is the proved projective intersection theorem; module finiteness
makes the final cut zero-dimensional. No dimension or properness of the
uncut quotient is supplied as an input. -/

noncomputable section
namespace CubicTenVariables.HomogeneousFiniteCutDimension
open MvPolynomial HessianTheorem11 HessianTheorem11.BibleHyperplanes
open HessianTheorem11.UnconditionalCutDimension TranslatedDepthSeven
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Iterating the proved single-cut inequality. The cuts need not be
independent, nonzero, or linear; their displayed degrees must be positive. -/
theorem dimension_le_of_homogeneous_cuts {n s : ℕ}
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z) (hc : IsAffineCone Z)
    (P : Fin s → GeometricPolynomial n) (d : Fin s → ℕ)
    (hd : ∀ i, 0 < d i) (hP : ∀ i, (P i).IsHomogeneous (d i))
    (b : ℕ)
    (hcut : affineDimension {x | x ∈ Z ∧ ∀ i, eval x (P i) = 0} ≤ (b : Dimension)) :
    affineDimension Z ≤ ((b + s : ℕ) : Dimension) := by
  induction s generalizing Z b with
  | zero => simpa using hcut
  | succ s ih =>
    let Z' : Set (GeometricPoint n) := {x | x ∈ Z ∧ eval x (P 0) = 0}
    have hZ' : AlgebraicallyClosedSet Z' := homogeneous_cut_closed Z hZ (P 0)
    have hc' : IsAffineCone Z' := homogeneous_cut_cone Z hc (P 0) (hP 0)
    have hcut' : affineDimension {x | x ∈ Z' ∧
        ∀ i : Fin s, eval x (P i.succ) = 0} ≤ (b : Dimension) := by
      have he : {x | x ∈ Z' ∧ ∀ i : Fin s, eval x (P i.succ) = 0} =
          {x | x ∈ Z ∧ ∀ i : Fin (s + 1), eval x (P i) = 0} := by
        ext x
        simp only [Z', Set.mem_setOf_eq, Fin.forall_fin_succ, and_assoc]
      simpa only [he] using hcut
    have hi := ih Z' hZ' hc' (fun i => P i.succ) (fun i => d i.succ)
      (fun i => hd i.succ) (fun i => hP i.succ) b hcut'
    simpa only [Nat.add_assoc] using
      homogeneousCutDimensionInput.bound_of_cut Z hZ hc (P 0) (d 0)
        (hd 0) (hP 0) (b + s) hi

/-- The form needed by an origin-only Macaulay certificate. -/
theorem dimension_le_of_linear_cuts_at_origin {n s : ℕ}
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z) (hc : IsAffineCone Z)
    (L : Fin s → GeometricPolynomial n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (horigin : ∀ x ∈ Z, (∀ i, eval x (L i) = 0) → x = 0) :
    affineDimension Z ≤ (s : Dimension) := by
  have hcut : affineDimension {x | x ∈ Z ∧ ∀ i, eval x (L i) = 0} ≤
      (0 : Dimension) := by
    calc
      _ ≤ affineDimension ({0} : Set (GeometricPoint n)) :=
        affineDimension_mono (fun x hx => horigin x hx.1 hx.2)
      _ = 0 := affineDimension_origin
  simpa using dimension_le_of_homogeneous_cuts Z hZ hc L (fun _ => 1)
    (fun _ => Nat.zero_lt_one) hL 0 hcut

/-- The simultaneous actual cuts are exactly the zero locus of the sum ideal. -/
theorem simultaneous_cuts_eq_zeroLocus {n s : ℕ}
    (I : Ideal (GeometricPolynomial n)) (L : Fin s → GeometricPolynomial n) :
    {x | x ∈ zeroLocus GeometricField I ∧ ∀ i, eval x (L i) = 0} =
      zeroLocus GeometricField (I ⊔ Ideal.span (Set.range L)) := by
  ext x
  constructor
  · rintro ⟨hx,hL⟩
    have h : I ⊔ Ideal.span (Set.range L) ≤ RingHom.ker (eval x) := by
      refine sup_le hx (Ideal.span_le.mpr ?_)
      rintro _ ⟨i,rfl⟩
      exact hL i
    exact h
  · intro hx
    exact ⟨fun f hf => hx f (Ideal.mem_sup_left hf),
      fun i => hx (L i) (Ideal.mem_sup_right (Ideal.subset_span ⟨i,rfl⟩))⟩

/-- A finite algebra over the geometric field has dimension at most zero,
including the zero ring and nonreduced quotients. -/
theorem zeroLocus_dimension_le_zero_of_finite {n : ℕ}
    (J : Ideal (GeometricPolynomial n))
    [Module.Finite GeometricField (GeometricPolynomial n ⧸ J)] :
    affineDimension (zeroLocus GeometricField J) ≤ 0 := by
  letI : Algebra.IsIntegral GeometricField (GeometricPolynomial n ⧸ J) :=
    Algebra.IsIntegral.of_finite _ _
  rw [affineDimension, vanishingIdeal_zeroLocus_eq_radical, quotient_radical_dimension]
  simpa only [ringKrullDim_eq_zero_of_field] using
    (ringKrullDim_le_of_isIntegral (R := GeometricField)
      (S := GeometricPolynomial n ⧸ J))

/-- Finite-dimensionality after `s` linear cuts bounds the dimension of the
original cone by `s`. The equation ideal need not be radical or proper. -/
theorem dimension_le_of_finite_linear_cut_quotient {n s : ℕ}
    (I : Ideal (GeometricPolynomial n))
    (hc : IsAffineCone (zeroLocus GeometricField I))
    (L : Fin s → GeometricPolynomial n) (hL : ∀ i, (L i).IsHomogeneous 1)
    [Module.Finite GeometricField
      (GeometricPolynomial n ⧸ (I ⊔ Ideal.span (Set.range L)))] :
    affineDimension (zeroLocus GeometricField I) ≤ (s : Dimension) := by
  have hcut : affineDimension
      {x | x ∈ zeroLocus GeometricField I ∧ ∀ i, eval x (L i) = 0} ≤
      (0 : Dimension) := by
    rw [simultaneous_cuts_eq_zeroLocus]
    exact zeroLocus_dimension_le_zero_of_finite _
  simpa using dimension_le_of_homogeneous_cuts (zeroLocus GeometricField I)
    (algebraicallyClosedSet_zeroLocus I) hc L (fun _ => 1)
    (fun _ => Nat.zero_lt_one) hL 0 hcut

/-- Homogeneity of the actual ideal implies scalar stability of its zero set. -/
theorem zeroLocus_cone_of_homogeneous {n : ℕ}
    (I : Ideal (GeometricPolynomial n))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) GeometricField)) :
    IsAffineCone (zeroLocus GeometricField I) := by
  intro a x hx f hf
  have hpieces : ∀ j, eval (a • x) (homogeneousComponent j f) = 0 := by
    intro j
    have hj := hI j hf
    change (MvPolynomial.decomposition.decompose' f j : GeometricPolynomial n) ∈ I at hj
    rw [MvPolynomial.decomposition.decompose'_apply] at hj
    have he := LocalCubicNormalForm.homogeneous_eval₂_common_scalar
      (homogeneousComponent j f) (homogeneousComponent_isHomogeneous _ _)
      (RingHom.id GeometricField) x a
    change eval₂ (RingHom.id GeometricField) (fun i => a * x i)
      (homogeneousComponent j f) = 0
    rw [he]
    change a ^ j * eval x (homogeneousComponent j f) = 0
    have hxj : eval x (homogeneousComponent j f) = 0 := hx _ hj
    rw [hxj, mul_zero]
  rw [← sum_homogeneousComponent f, map_sum]
  exact Finset.sum_eq_zero (fun j _ => hpieces j)

/-- The fully ideal-theoretic interface: no separate cone or cut-dimension
hypothesis, only homogeneity and a finite-module certificate for the cut. -/
theorem quotient_dimension_le_of_finite_linear_cuts {n s : ℕ}
    (I : Ideal (GeometricPolynomial n))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) GeometricField))
    (L : Fin s → GeometricPolynomial n) (hL : ∀ i, (L i).IsHomogeneous 1)
    [Module.Finite GeometricField
      (GeometricPolynomial n ⧸ (I ⊔ Ideal.span (Set.range L)))] :
    ringKrullDim (GeometricPolynomial n ⧸ I) ≤ (s : Dimension) := by
  have h := dimension_le_of_finite_linear_cut_quotient I
    (zeroLocus_cone_of_homogeneous I hI) L hL
  rwa [affineDimension, vanishingIdeal_zeroLocus_eq_radical,
    quotient_radical_dimension] at h

end CubicTenVariables.HomogeneousFiniteCutDimension
