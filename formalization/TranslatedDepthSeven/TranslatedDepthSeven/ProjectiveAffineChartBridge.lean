import TranslatedDepthSeven.ProjectiveConeHilbertShift
import TranslatedDepthSeven.IntegralLocalEquationMultiplicitySpecialization

/-!
# A prime projective component on the standard affine chart

This file proves, directly from homogeneous polynomials, the two algebraic
facts needed when a prime projective component is restricted to `X₀ = 1`:

* its dehomogenized ideal is prime, provided `X₀` is not in the projective
  prime; and
* its cumulative affine Hilbert function is the original projective Hilbert
  function, degree by degree.

The proof does not appeal to a packaged affine-chart theorem.  A polynomial
in the image ideal is first represented by one homogeneous polynomial in the
original ideal: its homogeneous components are multiplied by suitable powers
of `X₀` so that they all have the same degree.  Dehomogenization is injective
on each homogeneous piece, since fixed-degree homogenization is its inverse.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

universe u

variable {K : Type u} [Field K]

/-- Substitution `X_none = 1` is onto: a preimage of an affine polynomial is
obtained by renaming all its variables with `some`. -/
theorem multivariateDehomogenization_surjective (n : ℕ) :
    Function.Surjective
      (@multivariateDehomogenization K (Fin n) _).toRingHom := by
  intro f
  refine ⟨MvPolynomial.rename some f, ?_⟩
  exact multivariateDehomogenization_rename f

/-- On the homogeneous piece of degree `k`, dehomogenization is injective. -/
theorem multivariateDehomogenization_injective_of_isHomogeneous
    {n k : ℕ} {f g : MvPolynomial (Option (Fin n)) K}
    (hf : f.IsHomogeneous k) (hg : g.IsHomogeneous k)
    (hdehom : multivariateDehomogenization f =
      multivariateDehomogenization g) :
    f = g := by
  let e := degreeHomogenizationLinearEquiv K n k
  obtain ⟨a, ha⟩ := e.surjective ⟨f, hf⟩
  obtain ⟨b, hb⟩ := e.surjective ⟨g, hg⟩
  have hab : a = b := by
    apply Subtype.ext
    have ha' := congrArg
      (fun h : MvPolynomial (Option (Fin n)) K ↦
        multivariateDehomogenization h) (congrArg Subtype.val ha)
    have hb' := congrArg
      (fun h : MvPolynomial (Option (Fin n)) K ↦
        multivariateDehomogenization h) (congrArg Subtype.val hb)
    change multivariateDehomogenization
        (multivariateHomogenization a.1 k) =
      multivariateDehomogenization f at ha'
    change multivariateDehomogenization
        (multivariateHomogenization b.1 k) =
      multivariateDehomogenization g at hb'
    rw [multivariateDehomogenization_homogenization a.1 k
          ((MvPolynomial.mem_restrictTotalDegree (Fin n) k a.1).1 a.2)] at ha'
    rw [multivariateDehomogenization_homogenization b.1 k
          ((MvPolynomial.mem_restrictTotalDegree (Fin n) k b.1).1 b.2)] at hb'
    exact ha'.trans (hdehom.trans hb'.symm)
  exact congrArg Subtype.val (ha.symm.trans (hab ▸ hb))

/-- Homogenizing the dehomogenization of a homogeneous polynomial, back to
the same degree, recovers the polynomial.  The first conjunct records the
degree bound needed to make the homogenization lossless. -/
theorem multivariateHomogenization_dehomogenization_of_isHomogeneous
    {n k : ℕ} (f : MvPolynomial (Option (Fin n)) K)
    (hf : f.IsHomogeneous k) :
    (multivariateDehomogenization f).totalDegree ≤ k ∧
      multivariateHomogenization (multivariateDehomogenization f) k = f := by
  let e := degreeHomogenizationLinearEquiv K n k
  obtain ⟨a, ha⟩ := e.surjective ⟨f, hf⟩
  have haVal : multivariateHomogenization a.1 k = f :=
    congrArg Subtype.val ha
  have hadehom : a.1 = multivariateDehomogenization f := by
    have h := congrArg
      (fun h : MvPolynomial (Option (Fin n)) K ↦
        multivariateDehomogenization h) haVal
    change multivariateDehomogenization
        (multivariateHomogenization a.1 k) =
      multivariateDehomogenization f at h
    rw [multivariateDehomogenization_homogenization a.1 k
      ((MvPolynomial.mem_restrictTotalDegree (Fin n) k a.1).1 a.2)] at h
    exact h
  constructor
  · rw [← hadehom]
    exact (MvPolynomial.mem_restrictTotalDegree (Fin n) k a.1).1 a.2
  · rw [← hadehom]
    exact haVal

/-- Multiplying the homogenizing variable adjusts the target degree of a
homogenization. -/
theorem multivariateHomogenization_raise_degree
    {n a b : ℕ} (f : MvPolynomial (Fin n) K)
    (hfa : f.totalDegree ≤ a) (hab : a ≤ b) :
    multivariateHomogenization f b =
      X (none : Option (Fin n)) ^ (b - a) *
        multivariateHomogenization f a := by
  apply multivariateDehomogenization_injective_of_isHomogeneous
  · exact multivariateHomogenization_isHomogeneous f b
  · simpa only [Nat.sub_add_cancel hab] using
      (isHomogeneous_X_pow (R := K) (none : Option (Fin n)) (b - a)).mul
        (multivariateHomogenization_isHomogeneous f a)
  · rw [map_mul, map_pow, multivariateDehomogenization_X_none,
      one_pow, one_mul,
      multivariateDehomogenization_homogenization f b (hfa.trans hab),
      multivariateDehomogenization_homogenization f a hfa]

/-- The homogeneous alignment of `g`: multiply its degree-`j` component by
`X_none^(D-j)` so that every summand has degree `D`. -/
def homogeneousAlignment {n : ℕ}
    (g : MvPolynomial (Option (Fin n)) K) (D : ℕ) :
    MvPolynomial (Option (Fin n)) K :=
  ∑ j ∈ Finset.range (D + 1),
    X (none : Option (Fin n)) ^ (D - j) * homogeneousComponent j g

theorem homogeneousAlignment_isHomogeneous {n D : ℕ}
    (g : MvPolynomial (Option (Fin n)) K) :
    (homogeneousAlignment g D).IsHomogeneous D := by
  apply IsHomogeneous.sum
  intro j hj
  simp only [Finset.mem_range, Nat.lt_add_one_iff] at hj
  simpa only [Nat.sub_add_cancel hj] using
    (isHomogeneous_X_pow (R := K) (none : Option (Fin n)) (D - j)).mul
      (homogeneousComponent_isHomogeneous j g)

theorem multivariateDehomogenization_homogeneousAlignment
    {n : ℕ} (g : MvPolynomial (Option (Fin n)) K) :
    multivariateDehomogenization
        (homogeneousAlignment g g.totalDegree) =
      multivariateDehomogenization g := by
  rw [homogeneousAlignment, map_sum]
  simp only [map_mul, map_pow, multivariateDehomogenization_X_none,
    one_pow, one_mul]
  rw [← map_sum, g.sum_homogeneousComponent]

/-- Every member of the image of a homogeneous ideal admits one homogeneous
preimage which still belongs to the original ideal. -/
theorem exists_homogeneous_preimage_mem_of_mem_map_dehomogenization
    {n : ℕ} (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K))
    {f : MvPolynomial (Fin n) K}
    (hf : f ∈ Ideal.map multivariateDehomogenization.toRingHom I) :
    ∃ (D : ℕ) (g : MvPolynomial (Option (Fin n)) K),
      g.IsHomogeneous D ∧ g ∈ I ∧
        multivariateDehomogenization g = f := by
  obtain ⟨g, hgI, hgf⟩ :=
    (Ideal.mem_map_iff_of_surjective _
      (multivariateDehomogenization_surjective (K := K) n)).1 hf
  refine ⟨g.totalDegree, homogeneousAlignment g g.totalDegree,
    homogeneousAlignment_isHomogeneous g, ?_, ?_⟩
  · apply Ideal.sum_mem
    intro j hj
    apply I.mul_mem_left
    have hjmem := hI j hgI
    change (MvPolynomial.decomposition.decompose' g j :
      MvPolynomial (Option (Fin n)) K) ∈ I at hjmem
    simpa only [MvPolynomial.decomposition.decompose'_apply] using hjmem
  · rw [multivariateDehomogenization_homogeneousAlignment]
    exact hgf

/-- A homogeneous prime not containing the homogenizing variable remains
prime after restriction to the standard affine chart. -/
theorem map_multivariateDehomogenization_isPrime
    {n : ℕ} (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K))
    (hprime : I.IsPrime)
    (hX : X (none : Option (Fin n)) ∉ I) :
    (Ideal.map multivariateDehomogenization.toRingHom I).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    have hone : (1 : MvPolynomial (Fin n) K) ∈
        Ideal.map multivariateDehomogenization.toRingHom I := by
      rw [htop]
      simp
    obtain ⟨D, g, hgHom, hgI, hgDehom⟩ :=
      exists_homogeneous_preimage_mem_of_mem_map_dehomogenization
        I hI hone
    have hgRecover :=
      (multivariateHomogenization_dehomogenization_of_isHomogeneous g hgHom).2
    have hraise := multivariateHomogenization_raise_degree
      (n := n) (1 : MvPolynomial (Fin n) K) (a := 0) (b := D)
      (by simp) (Nat.zero_le D)
    have hgpow : X (none : Option (Fin n)) ^ D = g := by
      calc
        X (none : Option (Fin n)) ^ D =
            multivariateHomogenization (1 : MvPolynomial (Fin n) K) D := by
          rw [hraise]
          simp [multivariateHomogenization]
        _ = g := by simpa [hgDehom] using hgRecover
    have hpowI : X (none : Option (Fin n)) ^ D ∈ I := hgpow ▸ hgI
    cases D with
    | zero =>
        exact hprime.ne_top ((Ideal.eq_top_iff_one I).2 (by simpa using hpowI))
    | succ D =>
        exact hX (hprime.mem_of_pow_mem (D + 1) (by simpa using hpowI))
  · intro f g hfg
    by_cases hfzero : f = 0
    · left
      simp [hfzero]
    by_cases hgzero : g = 0
    · right
      simp [hgzero]
    obtain ⟨D, q, hqHom, hqI, hqDehom⟩ :=
      exists_homogeneous_preimage_mem_of_mem_map_dehomogenization
        I hI hfg
    have hdegree :=
      (multivariateHomogenization_dehomogenization_of_isHomogeneous q hqHom).1
    rw [hqDehom, totalDegree_mul_of_isDomain hfzero hgzero] at hdegree
    let a := f.totalDegree
    let b := D - a
    have hfa : f.totalDegree ≤ a := le_rfl
    have hgb : g.totalDegree ≤ b := by
      dsimp only [a, b]
      omega
    let F := multivariateHomogenization f a
    let G := multivariateHomogenization g b
    have hFGHom : (F * G).IsHomogeneous D := by
      have hab : a + b = D := by
        dsimp only [a, b]
        omega
      simpa only [hab] using
        (multivariateHomogenization_isHomogeneous f a).mul
          (multivariateHomogenization_isHomogeneous g b)
    have hFGDehom : multivariateDehomogenization (F * G) = f * g := by
      dsimp only [F, G]
      rw [map_mul,
        multivariateDehomogenization_homogenization f a hfa,
        multivariateDehomogenization_homogenization g b hgb]
    have hFGq : F * G = q :=
      multivariateDehomogenization_injective_of_isHomogeneous
        hFGHom hqHom (hFGDehom.trans hqDehom.symm)
    have hmem : F ∈ I ∨ G ∈ I :=
      hprime.mem_or_mem (hFGq ▸ hqI)
    exact hmem.imp
      (fun hF ↦ by
        apply Ideal.mem_map_of_mem multivariateDehomogenization.toRingHom at hF
        simpa [F, multivariateDehomogenization_homogenization f a hfa] using hF)
      (fun hG ↦ by
        apply Ideal.mem_map_of_mem multivariateDehomogenization.toRingHom at hG
        simpa [G, multivariateDehomogenization_homogenization g b hgb] using hG)

/-- Membership in the affine-chart ideal is equivalent to membership of any
lossless fixed-degree homogenization in the original homogeneous prime. -/
theorem mem_map_dehomogenization_iff_homogenization_mem
    {n k : ℕ} (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K))
    (hprime : I.IsPrime)
    (hX : X (none : Option (Fin n)) ∉ I)
    (f : MvPolynomial (Fin n) K) (hfk : f.totalDegree ≤ k) :
    f ∈ Ideal.map multivariateDehomogenization.toRingHom I ↔
      multivariateHomogenization f k ∈ I := by
  constructor
  · intro hf
    obtain ⟨D, g, hgHom, hgI, hgDehom⟩ :=
      exists_homogeneous_preimage_mem_of_mem_map_dehomogenization I hI hf
    have hdegree :=
      (multivariateHomogenization_dehomogenization_of_isHomogeneous g hgHom).1
    rw [hgDehom] at hdegree
    have hgRecover :=
      (multivariateHomogenization_dehomogenization_of_isHomogeneous g hgHom).2
    rw [hgDehom] at hgRecover
    have hminimal : multivariateHomogenization f f.totalDegree ∈ I := by
      have hfactor := multivariateHomogenization_raise_degree f le_rfl hdegree
      rw [hfactor] at hgRecover
      have hprod : X (none : Option (Fin n)) ^ (D - f.totalDegree) *
          multivariateHomogenization f f.totalDegree ∈ I := by
        rw [hgRecover]
        exact hgI
      rcases hprime.mem_or_mem hprod with hpow | hmin
      · exfalso
        by_cases hgap : D - f.totalDegree = 0
        · exact hprime.ne_top
            ((Ideal.eq_top_iff_one I).2 (by simpa [hgap] using hpow))
        · exact hX (hprime.mem_of_pow_mem (D - f.totalDegree) hpow)
      · exact hmin
    rw [multivariateHomogenization_raise_degree f le_rfl hfk]
    exact I.mul_mem_left _ hminimal
  · intro hf
    have hmap := Ideal.mem_map_of_mem
      multivariateDehomogenization.toRingHom hf
    simpa [multivariateDehomogenization_homogenization f k hfk] using hmap

/-- The projective degree-`k` quotient piece and the affine degree-at-most-`k`
quotient filtration of the standard chart have equal dimensions. -/
theorem finrank_projective_eq_affine_dehomogenization
    {n k : ℕ} (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K))
    (hprime : I.IsPrime)
    (hX : X (none : Option (Fin n)) ∉ I) :
    Module.finrank K (quotientHomogeneousComponent K (Option (Fin n)) I k) =
      Module.finrank K
        (affineHilbertFiltration K n
          (Ideal.map multivariateDehomogenization.toRingHom I) k) := by
  let e := degreeHomogenizationLinearEquiv K n k
  let qAff := affineHilbertFiltrationMap K n
    (Ideal.map multivariateDehomogenization.toRingHom I) k
  let qProj := quotientHomogeneousComponentMap K (Option (Fin n)) I k
  have hker : Submodule.map e.toLinearMap (LinearMap.ker qAff) =
      LinearMap.ker qProj := by
    ext g
    constructor
    · rintro ⟨f, hf, hfg⟩
      rw [mem_ker_quotientHomogeneousComponentMap_iff]
      rw [← hfg]
      change multivariateHomogenization f.1 k ∈ I
      apply (mem_map_dehomogenization_iff_homogenization_mem
        I hI hprime hX f.1
          ((MvPolynomial.mem_restrictTotalDegree (Fin n) k f.1).1 f.2)).1
      exact (mem_ker_affineHilbertFiltrationMap_iff K n
        (Ideal.map multivariateDehomogenization.toRingHom I) k f).1 hf
    · intro hg
      refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
      change e.symm g ∈ LinearMap.ker
        (affineHilbertFiltrationMap K n
          (Ideal.map multivariateDehomogenization.toRingHom I) k)
      rw [mem_ker_affineHilbertFiltrationMap_iff]
      apply (mem_map_dehomogenization_iff_homogenization_mem
        I hI hprime hX (e.symm g).1
          ((MvPolynomial.mem_restrictTotalDegree (Fin n) k (e.symm g).1).1
            (e.symm g).2)).2
      change (e (e.symm g)).1 ∈ I
      rw [e.apply_symm_apply]
      exact (mem_ker_quotientHomogeneousComponentMap_iff K n k I g).1 hg
  have hkerFinrank : Module.finrank K (LinearMap.ker qAff) =
      Module.finrank K (LinearMap.ker qProj) :=
    ((e.submoduleMap (LinearMap.ker qAff)).trans
      (LinearEquiv.ofEq _ _ hker)).finrank_eq
  have hAff := LinearMap.finrank_range_add_finrank_ker qAff
  have hProj := LinearMap.finrank_range_add_finrank_ker qProj
  rw [LinearMap.range_eq_top.mpr
      (affineHilbertFiltrationMap_surjective K n
        (Ideal.map multivariateDehomogenization.toRingHom I) k)] at hAff
  rw [LinearMap.range_eq_top.mpr
      (quotientHomogeneousComponentMap_surjective K n k I)] at hProj
  simp at hAff hProj
  have hdomain := e.finrank_eq
  have hkerFinrank' :
      Module.finrank K
          (LinearMap.ker (affineHilbertFiltrationMap K n
            (Ideal.map multivariateDehomogenization.toRingHom I) k)) =
        Module.finrank K
          (LinearMap.ker
            (quotientHomogeneousComponentMap K (Option (Fin n)) I k)) := by
    simpa only [qAff, qProj] using hkerFinrank
  have hAff' :
      Module.finrank K
          (affineHilbertFiltration K n
            (Ideal.map multivariateDehomogenization.toRingHom I) k) +
        Module.finrank K
          (LinearMap.ker (affineHilbertFiltrationMap K n
            (Ideal.map multivariateDehomogenization.toRingHom I) k)) =
        Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K k) := by
    simpa only [qAff] using hAff
  have hProj' :
      Module.finrank K
          (quotientHomogeneousComponent K (Option (Fin n)) I k) +
        Module.finrank K
          (LinearMap.ker
            (quotientHomogeneousComponentMap K (Option (Fin n)) I k)) =
        Module.finrank K
          (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K k) := by
    simpa only [qProj] using hProj
  have hdomain' :
      Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K k) =
        Module.finrank K
          (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K k) := by
    simpa only [e] using hdomain
  omega

/-! ## Consecutively indexed coordinates -/

/-- Renaming `Fin (n+1)` as `Option (Fin n)` and then setting `none` equal
to one is exactly the literal standard affine-chart homomorphism. -/
theorem multivariateDehomogenization_comp_finSuccRename
    (n : ℕ) :
    (@multivariateDehomogenization ℚ (Fin n) _).toRingHom.comp
        (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv n)).toRingHom =
      (@rationalDehomogenizeAtZeroHom n) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [multivariateDehomogenization,
      rationalDehomogenizeAtZeroHom]
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [multivariateDehomogenization,
        rationalDehomogenizeAtZeroHom,
        MvPolynomial.renameEquiv_apply]
    · simp [multivariateDehomogenization,
        rationalDehomogenizeAtZeroHom,
        MvPolynomial.renameEquiv_apply]

/-- The Option-indexed and consecutive-coordinate descriptions give the
same dehomogenized ideal. -/
theorem map_dehomogenization_map_finSuccRename
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) :
    Ideal.map multivariateDehomogenization.toRingHom
        (I.map (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv n))) =
      I.map rationalDehomogenizeAtZeroHom := by
  change Ideal.map multivariateDehomogenization.toRingHom
      (Ideal.map
        (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv n)).toRingHom I) = _
  rw [Ideal.map_map, multivariateDehomogenization_comp_finSuccRename]

/-- A homogeneous prime projective component which meets `X₀ ≠ 0` has a
prime standard affine-chart ideal. -/
theorem rationalStandardAffineChart_isPrime
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℚ))
    (hprime : I.IsPrime)
    (hX : X (0 : Fin (n + 1)) ∉ I) :
    (I.map rationalDehomogenizeAtZeroHom).IsPrime := by
  let e : MvPolynomial (Fin (n + 1)) ℚ ≃ₐ[ℚ]
      MvPolynomial (Option (Fin n)) ℚ :=
    MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv n)
  let J : Ideal (MvPolynomial (Option (Fin n)) ℚ) := I.map e
  have hJhomogeneous : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin n)) ℚ) := by
    simpa only [J, e] using
      map_renameEquiv_isHomogeneous (_root_.finSuccEquiv n) I hI
  have hJprime : J.IsPrime := by
    letI : I.IsPrime := hprime
    dsimp only [J, e]
    infer_instance
  have hJX : X (none : Option (Fin n)) ∉ J := by
    intro hmem
    obtain ⟨f, hfI, hfeq⟩ :=
      (Ideal.mem_map_iff_of_surjective e e.surjective).1 hmem
    have hfX : f = X (0 : Fin (n + 1)) := by
      apply e.injective
      rw [hfeq]
      simp [e, MvPolynomial.renameEquiv_apply]
    exact hX (hfX ▸ hfI)
  have hJchart := map_multivariateDehomogenization_isPrime
    J hJhomogeneous hJprime hJX
  rw [map_dehomogenization_map_finSuccRename] at hJchart
  exact hJchart

/-- Degree by degree, the standard affine-chart cumulative Hilbert function
is the projective Hilbert function of the original homogeneous prime. -/
theorem finrank_projectiveHilbertPiece_eq_rationalStandardAffineChart
    {n k : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℚ))
    (hprime : I.IsPrime)
    (hX : X (0 : Fin (n + 1)) ∉ I) :
    Module.finrank ℚ (projectiveHilbertPiece ℚ n I k) =
      Module.finrank ℚ
        (affineHilbertFiltration ℚ n
          (I.map rationalDehomogenizeAtZeroHom) k) := by
  let e : MvPolynomial (Fin (n + 1)) ℚ ≃ₐ[ℚ]
      MvPolynomial (Option (Fin n)) ℚ :=
    MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv n)
  let J : Ideal (MvPolynomial (Option (Fin n)) ℚ) := I.map e
  have hJhomogeneous : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin n)) ℚ) := by
    simpa only [J, e] using
      map_renameEquiv_isHomogeneous (_root_.finSuccEquiv n) I hI
  have hJprime : J.IsPrime := by
    letI : I.IsPrime := hprime
    dsimp only [J, e]
    infer_instance
  have hJX : X (none : Option (Fin n)) ∉ J := by
    intro hmem
    obtain ⟨f, hfI, hfeq⟩ :=
      (Ideal.mem_map_iff_of_surjective e e.surjective).1 hmem
    have hfX : f = X (0 : Fin (n + 1)) := by
      apply e.injective
      rw [hfeq]
      simp [e, MvPolynomial.renameEquiv_apply]
    exact hX (hfX ▸ hfI)
  calc
    Module.finrank ℚ (projectiveHilbertPiece ℚ n I k) =
        Module.finrank ℚ
          (quotientHomogeneousComponent ℚ (Option (Fin n)) J k) := by
      change Module.finrank ℚ
          (quotientHomogeneousComponent ℚ (Fin (n + 1)) I k) = _
      exact finrank_quotientHomogeneousComponent_map_renameEquiv
        ℚ (_root_.finSuccEquiv n) I k
    _ = Module.finrank ℚ
          (affineHilbertFiltration ℚ n
            (Ideal.map multivariateDehomogenization.toRingHom J) k) :=
      finrank_projective_eq_affine_dehomogenization
        J hJhomogeneous hJprime hJX
    _ = Module.finrank ℚ
          (affineHilbertFiltration ℚ n
            (I.map rationalDehomogenizeAtZeroHom) k) := by
      rw [show Ideal.map multivariateDehomogenization.toRingHom J =
          I.map rationalDehomogenizeAtZeroHom by
        simpa only [J, e] using map_dehomogenization_map_finSuccRename I]

/-- Projective Hilbert dimension and degree pass unchanged to the standard
affine chart.  This is the exact hypothesis required by Pila's theorem. -/
theorem hasAffineHilbertDimensionDegree_rationalStandardAffineChart
    {n r d : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℚ))
    (hprime : I.IsPrime)
    (hX : X (0 : Fin (n + 1)) ∉ I)
    (hprojective : HasProjectiveDimensionDegree I r d) :
    HasAffineHilbertDimensionDegree
      (I.map rationalDehomogenizeAtZeroHom) r d := by
  rcases hprojective with ⟨_hdim, hd, P, hPdegree, hPlc, k₀, hPeventual⟩
  refine ⟨rationalStandardAffineChart_isPrime I hI hprime hX,
    hd, P, hPdegree, hPlc, k₀, ?_⟩
  intro k hk
  rw [← finrank_projectiveHilbertPiece_eq_rationalStandardAffineChart
    I hI hprime hX]
  exact hPeventual k hk

end

end TranslatedDepthSeven
