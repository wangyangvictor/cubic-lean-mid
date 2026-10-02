import TranslatedDepthSeven.ProjectiveDegreeSpanSectionAlgebra

/-!
# Exact degree along a prime flag of linear sections

A list of homogeneous linear equations is applied one equation at a time.
If every cut is proper and the literal section ideal remains prime, the
projective degree is unchanged at every step.  This packages repeated use
of the already proved one-hyperplane Hilbert-difference theorem.

The prime-flag hypothesis is deliberately explicit.  No claim is made that
primality of only the final section forces the intermediate sections to be
prime.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- Apply a list of hypersurface equations successively to an ideal. -/
def iteratedLinearCutIdeal {R : Type u} [CommRing R]
    (I : Ideal R) : List R → Ideal R
  | [] => I
  | f :: cuts => iteratedLinearCutIdeal (I ⊔ Ideal.span ({f} : Set R)) cuts

/-- Every equation cuts properly, its literal section ideal is prime, and
the remaining equations have the same property on that new section. -/
def IsProperPrimeLinearCutFlag {R : Type u} [CommRing R]
    (I : Ideal R) : List R → Prop
  | [] => True
  | f :: cuts =>
      f ∉ I ∧
      (I ⊔ Ideal.span ({f} : Set R)).IsPrime ∧
      IsProperPrimeLinearCutFlag (I ⊔ Ideal.span ({f} : Set R)) cuts

@[simp]
theorem iteratedLinearCutIdeal_nil {R : Type u} [CommRing R]
    (I : Ideal R) :
    iteratedLinearCutIdeal I [] = I := rfl

@[simp]
theorem iteratedLinearCutIdeal_cons {R : Type u} [CommRing R]
    (I : Ideal R) (f : R) (cuts : List R) :
    iteratedLinearCutIdeal I (f :: cuts) =
      iteratedLinearCutIdeal (I ⊔ Ideal.span ({f} : Set R)) cuts := rfl

/-- Successive adjunction of a list is the same ideal as adjoining the set
of all entries at once.  Repetitions in the list are harmless. -/
theorem iteratedLinearCutIdeal_eq_sup_span_toFinset
    {R : Type u} [CommRing R] [DecidableEq R]
    (I : Ideal R) (cuts : List R) :
    iteratedLinearCutIdeal I cuts =
      I ⊔ Ideal.span (cuts.toFinset : Set R) := by
  induction cuts generalizing I with
  | nil => simp
  | cons f cuts ih =>
      rw [iteratedLinearCutIdeal_cons, ih, List.toFinset_cons]
      rw [show ((↑(insert f cuts.toFinset) : Set R)) =
          {f} ∪ (cuts.toFinset : Set R) by ext x; simp]
      rw [Ideal.span_union]
      ac_rfl

/-- Ring maps commute with adjoining a list of equations successively. -/
theorem map_iteratedLinearCutIdeal
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (cuts : List R) :
    (iteratedLinearCutIdeal I cuts).map φ =
      iteratedLinearCutIdeal (I.map φ) (cuts.map φ) := by
  induction cuts generalizing I with
  | nil => rfl
  | cons f cuts ih =>
      rw [iteratedLinearCutIdeal_cons, List.map_cons,
        iteratedLinearCutIdeal_cons, ih (I ⊔ Ideal.span ({f} : Set R)),
        Ideal.map_sup, Ideal.map_span]
      congr 2
      ext x
      simp

/-- The last ideal in a prime flag is prime. -/
theorem iteratedLinearCutIdeal_isPrime
    {R : Type u} [CommRing R]
    (I : Ideal R) (hI : I.IsPrime) (cuts : List R)
    (hflag : IsProperPrimeLinearCutFlag I cuts) :
    (iteratedLinearCutIdeal I cuts).IsPrime := by
  induction cuts generalizing I with
  | nil => simpa using hI
  | cons f cuts ih =>
      exact ih (I := I ⊔ Ideal.span ({f} : Set R)) hflag.2.1 hflag.2.2

/-- Homogeneous equations preserve homogeneity along the whole flag. -/
theorem iteratedLinearCutIdeal_isHomogeneous
    {K : Type u} [Field K] {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (cuts : List (MvPolynomial σ K))
    (hcuts : ∀ f ∈ cuts, f.IsHomogeneous 1) :
    (iteratedLinearCutIdeal I cuts).IsHomogeneous
      (homogeneousSubmodule σ K) := by
  induction cuts generalizing I with
  | nil => simpa using hI
  | cons f cuts ih =>
      have hf : f.IsHomogeneous 1 := hcuts f (by simp)
      have hnext :
          (I ⊔ Ideal.span ({f} : Set (MvPolynomial σ K))).IsHomogeneous
            (homogeneousSubmodule σ K) := by
        apply hI.sup
        apply Ideal.homogeneous_span
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst g
        exact ⟨1, hf⟩
      apply ih (I := I ⊔ Ideal.span ({f} : Set (MvPolynomial σ K))) hnext
      intro g hg
      exact hcuts g (by simp [hg])

/-- A proper prime flag of homogeneous linear sections preserves the exact
projective degree and drops the projective dimension by the flag length. -/
theorem iteratedLinearCutIdeal_preserves_projective_degree
    {K : Type u} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) K))
    (cuts : List (MvPolynomial (Fin (N + 1)) K))
    (hcuts : ∀ f ∈ cuts, f.IsHomogeneous 1)
    (hdegree : HasProjectiveDimensionDegree I (r + cuts.length) d)
    (hflag : IsProperPrimeLinearCutFlag I cuts) :
    HasProjectiveDimensionDegree (iteratedLinearCutIdeal I cuts) r d := by
  induction cuts generalizing I r with
  | nil =>
      simpa using hdegree
  | cons f cuts ih =>
      have hfhom : f.IsHomogeneous 1 := hcuts f (by simp)
      have hcutsTail : ∀ g ∈ cuts, g.IsHomogeneous 1 := by
        intro g hg
        exact hcuts g (by simp [hg])
      have hfirstHom :
          (I ⊔ Ideal.span ({f} : Set (MvPolynomial (Fin (N + 1)) K))).IsHomogeneous
            (homogeneousSubmodule (Fin (N + 1)) K) := by
        apply hIhom.sup
        apply Ideal.homogeneous_span
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst g
        exact ⟨1, hfhom⟩
      have hdimension : r + (f :: cuts).length = (r + cuts.length) + 1 := by
        simp only [List.length_cons]
        omega
      have hfirstDegree :
          HasProjectiveDimensionDegree
            (I ⊔ Ideal.span ({f} : Set (MvPolynomial (Fin (N + 1)) K)))
            (r + cuts.length) d := by
        apply projectiveSection_preserves_degree I hIprime hIhom
          (by simpa only [hdimension] using hdegree) f hfhom hflag.1 hflag.2.1
      exact ih
        (I := I ⊔ Ideal.span ({f} : Set (MvPolynomial (Fin (N + 1)) K)))
        hflag.2.1 hfirstHom hcutsTail hfirstDegree hflag.2.2

end

end TranslatedDepthSeven
