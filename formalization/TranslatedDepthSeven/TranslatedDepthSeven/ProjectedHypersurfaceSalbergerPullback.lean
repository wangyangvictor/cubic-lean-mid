import TranslatedDepthSeven.MarkedProjectionCountingBridge
import TranslatedDepthSeven.RankSevenSalbergerPilaTerminal
import TranslatedDepthSeven.IntegralLocalEquationMultiplicitySpecialization
import TranslatedDepthSeven.PrimitiveIntegralHypersurfaceClosure

/-!
# Salberger on a marked hypersurface image and pullback to the source

This file isolates the algebraic step used by the elementary marked-
projection proof.  Salberger's theorem is applied to the literal
hypersurface image, where a nonzero derivative of one primitive integral
equation supplies multiplicity one.  The resulting auxiliary form is then
pulled back along the displayed linear projection.

The derivative certificate concerns the image model only.  We make no
claim that it proves smooth reduction of the original source component:
the inverse of a finite birational projection may have additional bad
primes.  This distinction is exactly why the determinant theorem is used
on the image before the auxiliary form is pulled back.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Pullback of a homogeneous target polynomial by the displayed rows of a
projective linear map. -/
def projectiveMatrixPolynomialPullback
    {N c : ℕ} (A : Matrix (Fin c) (Fin N) ℚ)
    (F : MvPolynomial (Fin c) ℚ) : MvPolynomial (Fin N) ℚ :=
  MvPolynomial.aeval (StandardAG.projectiveMatrixLinearForm A) F

/-- Pullback along linear homogeneous coordinates preserves the degree of
a homogeneous polynomial. -/
theorem projectiveMatrixPolynomialPullback_isHomogeneous
    {N c k : ℕ} (A : Matrix (Fin c) (Fin N) ℚ)
    (hlinear : ∀ i,
      (StandardAG.projectiveMatrixLinearForm A i).IsHomogeneous 1)
    {F : MvPolynomial (Fin c) ℚ} (hF : F.IsHomogeneous k) :
    (projectiveMatrixPolynomialPullback A F).IsHomogeneous k := by
  simpa [projectiveMatrixPolynomialPullback] using
    hF.aeval (StandardAG.projectiveMatrixLinearForm A) hlinear

/-- Evaluation of a pulled-back polynomial is evaluation at the projected
homogeneous tuple. -/
theorem eval_projectiveMatrixPolynomialPullback
    {N c : ℕ} (A : Matrix (Fin c) (Fin N) ℚ)
    (x : Fin N → ℚ) (F : MvPolynomial (Fin c) ℚ) :
    MvPolynomial.eval x (projectiveMatrixPolynomialPullback A F) =
      MvPolynomial.eval
        (fun i ↦ MvPolynomial.eval x
          (StandardAG.projectiveMatrixLinearForm A i)) F := by
  change (MvPolynomial.aeval x)
      (MvPolynomial.aeval
        (StandardAG.projectiveMatrixLinearForm A) F) =
    MvPolynomial.aeval
      (fun i ↦ MvPolynomial.aeval x
        (StandardAG.projectiveMatrixLinearForm A i)) F
  rw [← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp

/-- A target form outside the scheme-theoretic image ideal pulls back to a
form outside the source ideal.  This is a kernel calculation, not a
set-theoretic dominance assertion. -/
theorem projectiveMatrixPolynomialPullback_not_mem_source
    {N c : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℚ))
    (A : Matrix (Fin c) (Fin N) ℚ)
    {F : MvPolynomial (Fin c) ℚ}
    (hF : F ∉ RingHom.ker
      (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom) :
    projectiveMatrixPolynomialPullback A F ∉ I := by
  intro hpullback
  apply hF
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk I
      (projectiveMatrixPolynomialPullback A F) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hpullback

/-- The one-equation affine chart used for the derivative certificate of a
projected hypersurface. -/
def projectedHypersurfaceAffineEquation
    {r : ℕ} (G : MvPolynomial (Fin (r + 2)) ℤ) :
    Fin 1 → MvPolynomial (Fin (r + 1)) ℤ :=
  fun _ ↦ integralDehomogenizeAtZeroHom G

/-- Selecting one affine coordinate for the one-equation Jacobian is
automatically injective. -/
def projectedHypersurfaceSelectedVariable
    {r : ℕ} (j : Fin (r + 1)) : Fin 1 → Fin (r + 1) :=
  fun _ ↦ j

theorem projectedHypersurfaceSelectedVariable_injective
    {r : ℕ} (j : Fin (r + 1)) :
    Function.Injective (projectedHypersurfaceSelectedVariable j) := by
  intro i i' _h
  exact Subsingleton.elim i i'

/-- If the contracted integral model of the rational image hypersurface is
the principal ideal of the displayed integral equation, then a nonzero
one-row Jacobian determinant at an integral affine point supplies exactly
the multiplicity-one statement used by Salberger at every prime not
dividing that determinant.

For a primitive integral equation the displayed closure equality is the
ordinary Gauss-lemma statement.  It is kept literal here so that no
unproved assertion about the source component's reduction is introduced. -/
theorem projectedHypersurface_multiplicityOne_of_integralEquation
    {r : ℕ}
    (I : Ideal (MvPolynomial (Fin (r + 2)) ℚ))
    (G : MvPolynomial (Fin (r + 2)) ℤ)
    (hclosure : projectiveIntegralClosureIdeal I = Ideal.span {G})
    (z : Fin (r + 1) → ℤ)
    (j : Fin (r + 1))
    (hpoint : MvPolynomial.eval z
      (integralDehomogenizeAtZeroHom G) = 0)
    (hminor : MvPolynomial.eval z
      (selectedJacobianDeterminant
        (projectedHypersurfaceAffineEquation G)
        (projectedHypersurfaceSelectedVariable j)) ≠ 0) :
    let Δ : ℤ := MvPolynomial.eval z
      (selectedJacobianDeterminant
        (projectedHypersurfaceAffineEquation G)
        (projectedHypersurfaceSelectedVariable j))
    Δ ≠ 0 ∧
      ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
        HasHilbertSamuelMultiplicityAt hp
          (projectiveSpecialFiberIdeal I)
          (fun i ↦ (integralAffineProjectivePoint z i : ZMod p)) r 1 := by
  let equations := projectedHypersurfaceAffineEquation G
  let selectedVar := projectedHypersurfaceSelectedVariable j
  have hmap : Ideal.map integralDehomogenizeAtZeroHom
      (Ideal.span {G}) = Ideal.span (Set.range equations) := by
    rw [Ideal.map_span]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro f ⟨g, hg, rfl⟩
      have hg' : g = G := by simpa using hg
      subst g
      exact Ideal.subset_span ⟨(0 : Fin 1), rfl⟩
    · apply Ideal.span_le.mpr
      rintro f ⟨i, rfl⟩
      exact Ideal.subset_span ⟨G, Set.mem_singleton G,
        by simp [equations, projectedHypersurfaceAffineEquation]⟩
  have hpointIdeal : ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
      (Ideal.span {G}), MvPolynomial.eval z f = 0 := by
    intro f hf
    rw [hmap] at hf
    have heval : Ideal.span (Set.range equations) ≤
        RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id ℤ) z) := by
      apply Ideal.span_le.mpr
      rintro f ⟨i, rfl⟩
      apply RingHom.mem_ker.mpr
      simpa [equations, projectedHypersurfaceAffineEquation] using hpoint
    exact RingHom.mem_ker.mp (heval hf)
  have hIJ : Ideal.span (Set.range equations) ≤
      Ideal.map integralDehomogenizeAtZeroHom (Ideal.span {G}) := by
    rw [hmap]
  have hclear : ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
      (Ideal.span {G}), (1 : MvPolynomial (Fin (r + 1)) ℤ) * f ∈
        Ideal.span (Set.range equations) := by
    intro f hf
    rw [hmap] at hf
    simpa using hf
  have hresult :=
    hasHilbertSamuelMultiplicityAt_one_of_integral_localEquations
      (J := Ideal.span {G}) z equations selectedVar
      (projectedHypersurfaceSelectedVariable_injective j)
      1 hpointIdeal hIJ hclear (by simp) hminor
  dsimp only
  constructor
  · exact hminor
  · intro p hp hpDelta
    have hp' := hresult.2 p hp
    rw [projectiveSpecialFiberIdeal, hclosure]
    exact hp' (by
      simpa [integralSelectedJacobianChartCertificate, equations,
        selectedVar] using hpDelta)

/-- For a primitive integral equation irreducible over `ℚ`, the closure
hypothesis in the preceding theorem is automatic by multivariable Gauss
lemma.  Thus the only excluded primes are the prime divisors of the
displayed nonzero derivative. -/
theorem projectedHypersurface_multiplicityOne_of_primitiveEquation
    {r : ℕ}
    (G : MvPolynomial (Fin (r + 2)) ℤ)
    (hprimitive : IsPrimitiveIntegralMvPolynomial G)
    (hirreducible :
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G))
    (z : Fin (r + 1) → ℤ)
    (j : Fin (r + 1))
    (hpoint : MvPolynomial.eval z
      (integralDehomogenizeAtZeroHom G) = 0)
    (hminor : MvPolynomial.eval z
      (selectedJacobianDeterminant
        (projectedHypersurfaceAffineEquation G)
        (projectedHypersurfaceSelectedVariable j)) ≠ 0) :
    let I : Ideal (MvPolynomial (Fin (r + 2)) ℚ) :=
      Ideal.span {MvPolynomial.map (Int.castRingHom ℚ) G}
    let Δ : ℤ := MvPolynomial.eval z
      (selectedJacobianDeterminant
        (projectedHypersurfaceAffineEquation G)
        (projectedHypersurfaceSelectedVariable j))
    Δ ≠ 0 ∧
      ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
        HasHilbertSamuelMultiplicityAt hp
          (projectiveSpecialFiberIdeal I)
          (fun i ↦ (integralAffineProjectivePoint z i : ZMod p)) r 1 := by
  dsimp only
  exact projectedHypersurface_multiplicityOne_of_integralEquation
    (Ideal.span {MvPolynomial.map (Int.castRingHom ℚ) G}) G
    (projectiveIntegralClosureIdeal_span_primitive G hprimitive hirreducible)
    z j hpoint hminor

/-- Salberger's auxiliary form on the projected hypersurface pulls back to
a homogeneous auxiliary form which avoids the original source and vanishes
at every source point whose projected integral representative belongs to
the prescribed Salberger residue class. -/
theorem exists_projectedHypersurface_salbergerPullback
    (hSalberger : Salberger2007Corollary37)
    {N r d : ℕ} {epsilon B : ℝ}
    (hepsilon : 0 < epsilon)
    (hr : 1 ≤ r)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIprime : I.IsPrime)
    (marked : Fin (N + 1) → ℚ)
    (hmarked : I ≤ RingHom.ker (MvPolynomial.aeval marked).toRingHom)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection : StandardAG.IsMarkedFiniteBirationalLinearProjection
      (d := d) I hIprime marked hmarked A G)
    (hImage : IsReducedEquidimensionalProjectiveScheme
      (RingHom.ker
        (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom) r d)
    (hInfinity : InfinityHyperplaneMeetsProperly
      (RingHom.ker
        (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom))
    (hB : 1 ≤ B)
    {index : Type} [Fintype index]
    (prime : index → ℕ)
    (hprime : ∀ i, (prime i).Prime)
    (hinjective : Function.Injective prime)
    (point : ∀ i, Fin (r + 2) → ZMod (prime i))
    (hchart : ∀ i, point i 0 ≠ 0)
    (hmultiplicity : ∀ i,
      HasHilbertSamuelMultiplicityAt (hprime i)
        (projectiveSpecialFiberIdeal
          (RingHom.ker
            (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom))
        (point i) r 1)
    (hproduct : B ^ (1 + epsilon) ≤
      ∏ i, (prime i : ℝ) ^
        (((d : ℝ) / (1 : ℝ)) ^ ((r : ℝ)⁻¹))) :
    ∃ K k : ℕ,
    ∃ F : MvPolynomial (Fin (r + 2)) ℚ,
      k ≤ K ∧ F.IsHomogeneous k ∧
      F ∉ RingHom.ker
        (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom ∧
      (projectiveMatrixPolynomialPullback A F).IsHomogeneous k ∧
      projectiveMatrixPolynomialPullback A F ∉ I ∧
      ∀ (x : Fin (N + 1) → ℚ)
        (xImage : Fin (r + 2) → ℤ),
        (∀ i, (xImage i : ℚ) = MvPolynomial.eval x
          (StandardAG.projectiveMatrixLinearForm A i)) →
        InSalbergerSOne
          (RingHom.ker
            (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom)
          B prime point xImage →
        MvPolynomial.eval x (projectiveMatrixPolynomialPullback A F) = 0 := by
  let imageIdeal := RingHom.ker
    (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom
  obtain ⟨hlinear, _hfinite, _hkernel, _hGhomogeneous, _hGirred,
      _hdegreeOne, _hmarkedChart, _hmarkedFibre, _hfibres⟩ := hprojection
  obtain ⟨K, k, F, hk, hFhomogeneous, hFnot, hFzero⟩ :=
    salberger2007_corollary37_multiplicityOne
      hSalberger hepsilon imageIdeal hr hImage hInfinity hB
        prime hprime hinjective point hchart hmultiplicity hproduct
  refine ⟨K, k, F, hk, hFhomogeneous, hFnot,
    projectiveMatrixPolynomialPullback_isHomogeneous A hlinear
      hFhomogeneous,
    projectiveMatrixPolynomialPullback_not_mem_source I A hFnot, ?_⟩
  intro x xImage hxImage hxSalberger
  rw [eval_projectiveMatrixPolynomialPullback]
  have hzero := hFzero xImage hxSalberger
  calc
    MvPolynomial.eval
        (fun i ↦ MvPolynomial.eval x
          (StandardAG.projectiveMatrixLinearForm A i)) F =
        MvPolynomial.eval (fun i ↦ (xImage i : ℚ)) F := by
      apply congrArg (fun y : Fin (r + 2) → ℚ ↦ MvPolynomial.eval y F)
      funext i
      exact (hxImage i).symm
    _ = 0 := hzero

/-- The coefficient-uniform form of the preceding construction.  The
degree bound for the auxiliary form is chosen immediately after the
image dimension `r`, degree `d`, and `epsilon`, before the source ideal,
marked projection, residue primes, and points. -/
theorem exists_uniform_projectedHypersurface_salbergerPullback
    (hSalberger : Salberger2007Corollary37)
    {N r d : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hr : 1 ≤ r) :
    ∃ K : ℕ,
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
        (hIprime : I.IsPrime)
        (marked : Fin (N + 1) → ℚ)
        (hmarked : I ≤
          RingHom.ker (MvPolynomial.aeval marked).toRingHom),
      ∀ (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
        (G : MvPolynomial (Fin (r + 2)) ℚ)
        (hprojection : StandardAG.IsMarkedFiniteBirationalLinearProjection
          (d := d) I hIprime marked
            hmarked A G)
        (hImage : IsReducedEquidimensionalProjectiveScheme
          (RingHom.ker
            (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom) r d)
        (hInfinity : InfinityHyperplaneMeetsProperly
          (RingHom.ker
            (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom)),
      ∀ (B : ℝ) (hB : 1 ≤ B),
      ∀ (index : Type) (_ : Fintype index)
        (prime : index → ℕ)
        (hprime : ∀ i, (prime i).Prime)
        (hinjective : Function.Injective prime)
        (point : ∀ i, Fin (r + 2) → ZMod (prime i))
        (hchart : ∀ i, point i 0 ≠ 0)
        (hmultiplicity : ∀ i,
          HasHilbertSamuelMultiplicityAt (hprime i)
            (projectiveSpecialFiberIdeal
              (RingHom.ker
                (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom))
            (point i) r 1)
        (hproduct : B ^ (1 + epsilon) ≤
          ∏ i, (prime i : ℝ) ^
            (((d : ℝ) / (1 : ℝ)) ^ ((r : ℝ)⁻¹))),
        ∃ k : ℕ, ∃ F : MvPolynomial (Fin (r + 2)) ℚ,
          k ≤ K ∧ F.IsHomogeneous k ∧
          F ∉ RingHom.ker
            (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom ∧
          (projectiveMatrixPolynomialPullback A F).IsHomogeneous k ∧
          projectiveMatrixPolynomialPullback A F ∉ I ∧
          ∀ (x : Fin (N + 1) → ℚ)
            (xImage : Fin (r + 2) → ℤ),
            (∀ i, (xImage i : ℚ) = MvPolynomial.eval x
              (StandardAG.projectiveMatrixLinearForm A i)) →
            InSalbergerSOne
              (RingHom.ker
                (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom)
              B prime point xImage →
            MvPolynomial.eval x
              (projectiveMatrixPolynomialPullback A F) = 0 := by
  obtain ⟨K, hK⟩ := hSalberger (r + 1) d epsilon hepsilon
  refine ⟨K, ?_⟩
  intro I hIprime marked hmarked A G hprojection hImage hInfinity
    B hB index instIndex prime hprime hinjective point hchart hmultiplicity
    hproduct
  letI : Fintype index := instIndex
  let imageIdeal := RingHom.ker
    (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom
  obtain ⟨hlinear, _hfinite, _hkernel, _hGhomogeneous, _hGirred,
      _hdegreeOne, _hmarkedChart, _hmarkedFibre, _hfibres⟩ := hprojection
  have hproduct' :
      B ^ (1 + epsilon) ≤
        ∏ i, (prime i : ℝ) ^
          (((d : ℝ) / ((1 : ℕ) : ℝ)) ^ ((r : ℝ)⁻¹)) := by
    simpa using hproduct
  obtain ⟨k, F, hk, hFhomogeneous, hFnot, hFzero⟩ :=
    hK r hr imageIdeal hImage hInfinity B hB index instIndex
      prime hprime hinjective (fun _ ↦ 1) (fun _ ↦ Nat.zero_lt_succ 0)
      point hchart hmultiplicity hproduct'
  refine ⟨k, F, hk, hFhomogeneous, hFnot,
    projectiveMatrixPolynomialPullback_isHomogeneous A hlinear
      hFhomogeneous,
    projectiveMatrixPolynomialPullback_not_mem_source I A hFnot, ?_⟩
  intro x xImage hxImage hxSalberger
  rw [eval_projectiveMatrixPolynomialPullback]
  have hzero := hFzero xImage hxSalberger
  calc
    MvPolynomial.eval
        (fun i ↦ MvPolynomial.eval x
          (StandardAG.projectiveMatrixLinearForm A i)) F =
        MvPolynomial.eval (fun i ↦ (xImage i : ℚ)) F := by
      apply congrArg (fun y : Fin (r + 2) → ℚ ↦ MvPolynomial.eval y F)
      funext i
      exact (hxImage i).symm
    _ = 0 := hzero

end

end TranslatedDepthSeven
