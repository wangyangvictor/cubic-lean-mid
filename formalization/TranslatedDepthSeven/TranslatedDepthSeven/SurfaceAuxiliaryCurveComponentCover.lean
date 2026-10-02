import TranslatedDepthSeven.CanonicalHomogeneousComponentBezoutInternal

/-! A finite family of proper homogeneous cuts on an actual rational prime
surface produces a finite family of actual prime homogeneous curves. The
component dimensions, degrees, degree sum and point coverage are proved
internally. Components repeated across cuts are counted only once. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000

/-- The literal deduplicated minimal-prime components of the displayed cuts. -/
def surfaceAuxiliaryCurveComponents {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (A : Finset (MvPolynomial (Fin (N + 1)) ℚ)) :
    Finset (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) := by
  classical
  exact A.biUnion fun G => finiteMinimalPrimes (I ⊔ Ideal.span {G})

@[simp] theorem mem_surfaceAuxiliaryCurveComponents_iff {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (A : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (P : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    P ∈ surfaceAuxiliaryCurveComponents I A ↔
      ∃ G ∈ A, P ∈ finiteMinimalPrimes (I ⊔ Ideal.span {G}) := by
  classical
  simp [surfaceAuxiliaryCurveComponents]

/-- Canonical Hilbert degree is independent of which cut a component came from. -/
theorem surfaceAuxiliaryCurveComponents_certificate
    {N d e : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (A : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (hA : ∀ G ∈ A, G.IsHomogeneous e ∧ G ∉ I)
    (P : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hP : P ∈ surfaceAuxiliaryCurveComponents I A) :
    P.IsPrime ∧ P.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) ∧
      I ≤ P ∧ HasProjectiveDimensionDegree P 1 (projectiveDimensionDegreeWeight 1 P) := by
  obtain ⟨G, hGA, hPG⟩ := (mem_surfaceAuxiliaryCurveComponents_iff I A P).mp hP
  obtain ⟨deg, hdeg, _⟩ := properHomogeneousHypersurface_componentDimensionDegreeMass
    (projectiveHilbertDegreeCertification_internal ℚ) I G hprime hhom hdegree
    (hA G hGA).1 (hA G hGA).2
  have hcut : (I ⊔ Ideal.span {G}).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) ℚ) := by
    apply hhom.sup
    apply Ideal.homogeneous_span
    intro f hf
    exact ⟨e, (Set.mem_singleton_iff.mp hf).symm ▸ (hA G hGA).1⟩
  refine ⟨isPrime_of_mem_finiteMinimalPrimes hPG,
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hcut
      ((mem_finiteMinimalPrimes_iff _ _).mp hPG),
    le_sup_left.trans (le_of_mem_finiteMinimalPrimes hPG), ?_⟩
  have heq : projectiveDimensionDegreeWeight 1 P = deg P := by
    simpa using projectiveDimensionDegreeWeight_eq (B := 1) (hdeg P hPG)
  rw [heq]
  exact hdeg P hPG

/-- Each curve has degree at most the product of the fixed surface and cut
degrees, independently of the size of the auxiliary family. -/
theorem surfaceAuxiliaryCurveComponents_degree_le
    {N d e : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (A : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (hA : ∀ G ∈ A, G.IsHomogeneous e ∧ G ∉ I)
    (P : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hP : P ∈ surfaceAuxiliaryCurveComponents I A) :
    projectiveDimensionDegreeWeight 1 P ≤ d * e := by
  obtain ⟨G, hGA, hPG⟩ := (mem_surfaceAuxiliaryCurveComponents_iff I A P).mp hP
  obtain ⟨deg, hdeg, hmass⟩ := properHomogeneousHypersurface_componentDimensionDegreeMass
    (projectiveHilbertDegreeCertification_internal ℚ) I G hprime hhom hdegree
    (hA G hGA).1 (hA G hGA).2
  have heq : projectiveDimensionDegreeWeight 1 P = deg P := by
    simpa using projectiveDimensionDegreeWeight_eq (B := 1) (hdeg P hPG)
  rw [heq]
  exact (Finset.single_le_sum (fun Q _ => Nat.zero_le (deg Q)) hPG).trans hmass

/-- Deduplication across different cuts cannot increase total curve degree. -/
theorem surfaceAuxiliaryCurveComponents_degree_sum_le
    {N d e : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (A : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (hA : ∀ G ∈ A, G.IsHomogeneous e ∧ G ∉ I) :
    ∑ P ∈ surfaceAuxiliaryCurveComponents I A, projectiveDimensionDegreeWeight 1 P ≤
      d * e * A.card := by
  classical
  have hsingle (G : MvPolynomial (Fin (N + 1)) ℚ) (hG : G ∈ A) :
      ∑ P ∈ finiteMinimalPrimes (I ⊔ Ideal.span {G}), projectiveDimensionDegreeWeight 1 P ≤
        d * e := by
    obtain ⟨deg, hdeg, hmass⟩ := properHomogeneousHypersurface_componentDimensionDegreeMass
      (projectiveHilbertDegreeCertification_internal ℚ) I G hprime hhom hdegree
      (hA G hG).1 (hA G hG).2
    calc
      _ = ∑ P ∈ finiteMinimalPrimes (I ⊔ Ideal.span {G}), deg P := by
        apply Finset.sum_congr rfl
        intro P hP
        simpa using projectiveDimensionDegreeWeight_eq (B := 1) (hdeg P hP)
      _ ≤ d * e := hmass
  suffices h : ∀ S : Finset (MvPolynomial (Fin (N + 1)) ℚ), S ⊆ A →
      ∑ P ∈ surfaceAuxiliaryCurveComponents I S, projectiveDimensionDegreeWeight 1 P ≤
        d * e * S.card from h A (Finset.Subset.refl A)
  intro S
  induction S using Finset.induction_on with
  | empty => simp [surfaceAuxiliaryCurveComponents]
  | @insert G S hGS ih =>
    intro hSA
    have hG := hsingle G (hSA (Finset.mem_insert_self _ _))
    have hS := ih (fun f hf => hSA (Finset.mem_insert_of_mem hf))
    have hunion := Finset.sum_union_inter
      (s₁ := finiteMinimalPrimes (I ⊔ Ideal.span {G}))
      (s₂ := surfaceAuxiliaryCurveComponents I S) (f := projectiveDimensionDegreeWeight 1)
    simp only [surfaceAuxiliaryCurveComponents, Finset.biUnion_insert,
      Finset.card_insert_of_notMem hGS, Nat.mul_add, Nat.mul_one] at *
    omega

/-- Actual rational zero vectors of the cuts are covered by actual component
ideals. This also includes the origin; no projective representative choice is
needed in this algebraic coverage statement. -/
theorem surfaceAuxiliaryCurveComponents_cover_iff {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (A : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (x : Fin (N + 1) → ℚ) :
    (∃ P ∈ surfaceAuxiliaryCurveComponents I A, x ∈ affineIdealZeroLocus P) ↔
      x ∈ affineIdealZeroLocus I ∧ ∃ G ∈ A, eval x G = 0 := by
  constructor
  · rintro ⟨P, hP, hx⟩
    obtain ⟨G, hGA, hPG⟩ := (mem_surfaceAuxiliaryCurveComponents_iff I A P).mp hP
    have hle := le_of_mem_finiteMinimalPrimes hPG
    exact ⟨fun f hf => hx f ((le_sup_left.trans hle) hf), G, hGA,
      hx G ((le_sup_right.trans hle) (Ideal.subset_span (Set.mem_singleton G)))⟩
  · rintro ⟨hx, G, hGA, hxG⟩
    let Q := RingHom.ker (MvPolynomial.eval x)
    letI : Q.IsPrime := RingHom.ker_isPrime (MvPolynomial.eval x)
    have hle : I ⊔ Ideal.span {G} ≤ Q := by
      apply sup_le
      · intro f hf
        exact hx f hf
      · apply Ideal.span_le.mpr
        intro f hf
        obtain rfl := Set.mem_singleton_iff.mp hf
        exact hxG
    obtain ⟨P, hP, hPQ⟩ := exists_finiteMinimalPrime_le hle
    exact ⟨P, (mem_surfaceAuxiliaryCurveComponents_iff I A P).mpr ⟨G, hGA, hP⟩,
      fun f hf => hPQ hf⟩

/-- A finite proper-cut family on the fixed surface yields a finite set of
prime rational curve ideals, covering exactly those cut points. All component
data are constructed; the only geometric premises describe the source surface. -/
theorem exists_surfaceAuxiliary_primeCurve_cover
    {N d e : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (A : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (hA : ∀ G ∈ A, G.IsHomogeneous e ∧ G ∉ I) :
    ∃ C : Finset (Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
      ∃ degree : Ideal (MvPolynomial (Fin (N + 1)) ℚ) → ℕ,
        (∀ P ∈ C, P.IsPrime ∧
          P.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) ∧
          I ≤ P ∧ HasProjectiveDimensionDegree P 1 (degree P) ∧ degree P ≤ d * e) ∧
        (∑ P ∈ C, degree P) ≤ d * e * A.card ∧
        C.card ≤ d * e * A.card ∧
        ∀ x : Fin (N + 1) → ℚ,
          (∃ P ∈ C, x ∈ affineIdealZeroLocus P) ↔
            x ∈ affineIdealZeroLocus I ∧ ∃ G ∈ A, eval x G = 0 := by
  classical
  let C := surfaceAuxiliaryCurveComponents I A
  let degree := projectiveDimensionDegreeWeight (N := N) 1
  have hcert := surfaceAuxiliaryCurveComponents_certificate I hprime hhom hdegree A hA
  have hmass := surfaceAuxiliaryCurveComponents_degree_sum_le I hprime hhom hdegree A hA
  refine ⟨C, degree, ?_, hmass, ?_, surfaceAuxiliaryCurveComponents_cover_iff I A⟩
  · intro P hP
    obtain ⟨hp, hh, hi, hd⟩ := hcert P hP
    exact ⟨hp, hh, hi, hd,
      surfaceAuxiliaryCurveComponents_degree_le I hprime hhom hdegree A hA P hP⟩
  ·
    calc
      C.card = ∑ _P ∈ C, 1 := by simp
      _ ≤ ∑ P ∈ C, degree P := Finset.sum_le_sum (fun P hP => (hcert P hP).2.2.2.2.1)
      _ ≤ d * e * A.card := hmass

end
end TranslatedDepthSeven
