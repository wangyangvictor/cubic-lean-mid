import TranslatedDepthSeven.HomogeneousNormalizationFibreDegreeInternal

/-!
# Distinct geometric points in every normalization fibre

The coefficient field and the residue field of the fibre need not agree.
A finite collection of algebra homomorphisms to any extension field can
be separated by one source element, because finitely many proper kernels
cannot cover a vector space over an infinite field. Its monic equation
over the normal polynomial base then bounds all exceptional fibres too.

The final theorem also permits additional target coordinates: fixing them
only restricts a fibre of the original normalization. No projection menu,
genericity, flatness, or scheme-theoretic fibre-length estimate is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial Published
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000

universe u v

/-- Distinct extension-field-valued algebra homomorphisms are separated by
one element of the source algebra. -/
theorem exists_element_injective_on_finite_algHoms_over_extension
    {K A : Type u} {L : Type v} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Field L] [Algebra K L]
    (S : Finset (A →ₐ[K] L)) :
    ∃ a : A, Set.InjOn (fun f : A →ₐ[K] L ↦ f a) (↑S : Set (A →ₐ[K] L)) := by
  classical
  let pairs := {p : S × S // p.1 ≠ p.2}
  let difference : pairs → A →ₗ[K] L := fun p ↦
    p.val.1.val.toLinearMap - p.val.2.val.toLinearMap
  have hproper : ∀ p, LinearMap.ker (difference p) ≠ ⊤ := by
    intro p hker
    apply p.property
    apply Subtype.ext
    ext a
    have ha : a ∈ LinearMap.ker (difference p) := by rw [hker]; trivial
    have hz := LinearMap.mem_ker.mp ha
    exact sub_eq_zero.mp hz
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun p ↦ LinearMap.ker (difference p)) hproper
  refine ⟨a, ?_⟩
  intro f hf g hg heq
  by_contra hfg
  let p : pairs := ⟨(⟨f, hf⟩, ⟨g, hg⟩), fun h ↦ hfg (congrArg Subtype.val h)⟩
  apply ha p
  exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr heq)

/-- The monic specialization bound for arbitrary extension-field-valued
points, not just points valued in the coefficient field itself. -/
theorem finite_extension_fibre_card_le_localized_rank
    {K B A : Type u} {L : Type v} [Field K] [Infinite K]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [CommRing A] [IsDomain A] [Algebra B A] [Algebra K A]
    [Field L] [Algebra K L] [FaithfulSMul B A] [Module.Finite B A]
    (specialization : B →+* L) (S : Finset (A →ₐ[K] L))
    (hS : ∀ f ∈ S, ∀ b : B, f (algebraMap B A b) = specialization b) :
    S.card ≤ Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) := by
  classical
  obtain ⟨a, hseparates⟩ := exists_element_injective_on_finite_algHoms_over_extension S
  obtain ⟨p, hmonic, hdegree, hzero⟩ :=
    exists_monic_annihilator_natDegree_le_localized_rank (B := B) a
  let q := p.map specialization
  have hqne : q ≠ 0 := Polynomial.map_monic_ne_zero hmonic
  have hroots : ∀ f ∈ S, q.eval (f a) = 0 := by
    intro f hf
    have hcomp : f.toRingHom.comp (algebraMap B A) = specialization := by
      ext b
      exact hS f hf b
    have h := congrArg f hzero
    have heval := Polynomial.hom_eval₂ p (algebraMap B A) f.toRingHom a
    rw [hcomp] at heval
    have hz : p.eval₂ specialization (f a) = 0 :=
      heval.symm.trans (by simpa only [map_zero] using h)
    simpa only [q, ← Polynomial.eval₂_eq_eval_map] using hz
  have hcard : S.card ≤ q.natDegree := by
    by_contra h
    have hsmall : q.natDegree < Fintype.card S := by simpa using (Nat.lt_of_not_ge h)
    have hinj : Function.Injective (fun f : S ↦ f.val a) := by
      intro f g hfg
      exact Subtype.ext (hseparates f.property g.property hfg)
    exact hqne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q hinj
      (fun f ↦ hroots f.val f.property) hsmall)
  exact hcard.trans ((Polynomial.natDegree_map_le).trans hdegree)

/-- The full set of geometric points in a fibre of a homogeneous linear
normalization is finite and has at most the projective degree many points. -/
theorem homogeneousNormalization_geometric_fibre_finite_ncard_le_degree
    {K : Type u} {L : Type v} [Field K] [CharZero K]
    [Field L] [Algebra K L] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hprime : I.IsPrime) (D : HomogeneousLinearNormalizationData I)
    (hdegree : HasProjectiveDimensionDegree I r d)
    (specialization : MvPolynomial (Fin D.parameterCount) K →ₐ[K] L) :
    Set.Finite {f : (MvPolynomial (Fin (N + 1)) K ⧸ I) →ₐ[K] L |
      f.comp D.hom = specialization} ∧
    Set.ncard {f : (MvPolynomial (Fin (N + 1)) K ⧸ I) →ₐ[K] L |
      f.comp D.hom = specialization} ≤ d := by
  classical
  letI : I.IsPrime := hprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  letI : Module.Finite B A := D.hom_finite
  let F : Set (A →ₐ[K] L) := {f | f.comp D.hom = specialization}
  have hbound (S : Finset (A →ₐ[K] L)) (hS : (S : Set _) ⊆ F) : S.card ≤ d := by
    have h := finite_extension_fibre_card_le_localized_rank
      (B := B) (A := A) specialization.toRingHom S (by
        intro f hf b
        exact congrArg (fun g : B →ₐ[K] L ↦ g b) (hS hf))
    exact h.trans
      (homogeneousLinearNormalization_genericRank_le_projectiveDegree I hprime D hdegree).2
  have hfinite : F.Finite := by
    by_contra h
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq h (d + 1)
    have hle := hbound S hS
    omega
  refine ⟨hfinite, ?_⟩
  have hle := hbound hfinite.toFinset (by simp)
  change F.ncard ≤ d
  rw [Set.ncard_eq_toFinset_card F hfinite]
  exact hle

/-- Any target containing all normalization coordinates has the same
uniform geometric fibre bound. This applies to appending the extra
primitive coordinate for a birational hypersurface projection. -/
theorem homogeneousNormalization_refined_geometric_fibre_finite_ncard_le_degree
    {K : Type u} {L : Type v} [Field K] [CharZero K]
    [Field L] [Algebra K L] {N r d k : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hprime : I.IsPrime) (D : HomogeneousLinearNormalizationData I)
    (hdegree : HasProjectiveDimensionDegree I r d)
    (h : MvPolynomial (Fin k) K →ₐ[K] (MvPolynomial (Fin (N + 1)) K ⧸ I))
    (j : MvPolynomial (Fin D.parameterCount) K →ₐ[K] MvPolynomial (Fin k) K)
    (hfactor : h.comp j = D.hom)
    (y : MvPolynomial (Fin k) K →ₐ[K] L) :
    Set.Finite {f : (MvPolynomial (Fin (N + 1)) K ⧸ I) →ₐ[K] L | f.comp h = y} ∧
    Set.ncard {f : (MvPolynomial (Fin (N + 1)) K ⧸ I) →ₐ[K] L | f.comp h = y} ≤ d := by
  have hsub : {f : (MvPolynomial (Fin (N + 1)) K ⧸ I) →ₐ[K] L | f.comp h = y} ⊆
      {f : (MvPolynomial (Fin (N + 1)) K ⧸ I) →ₐ[K] L | f.comp D.hom = y.comp j} := by
    intro f hf
    change f.comp h = y at hf
    change f.comp D.hom = y.comp j
    rw [← hfactor, ← AlgHom.comp_assoc, hf]
  obtain ⟨hfinite, hcard⟩ := homogeneousNormalization_geometric_fibre_finite_ncard_le_degree
    I hprime D hdegree (y.comp j)
  exact ⟨hfinite.subset hsub, (Set.ncard_le_ncard hsub hfinite).trans hcard⟩

end
end TranslatedDepthSeven
