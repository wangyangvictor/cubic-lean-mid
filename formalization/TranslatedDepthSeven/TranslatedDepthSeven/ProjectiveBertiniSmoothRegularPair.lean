import TranslatedDepthSeven.ProjectiveBertiniSmoothCoordinateNonzero
import TranslatedDepthSeven.ProjectiveBertiniIncidenceShrinking
import TranslatedDepthSeven.ProjectiveBertiniIncidenceLocalization
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# A literal regular coordinate pair near a smooth marked point

Two coordinates omitted by a selected Jacobian minor give a genuine
regular pair on a principal neighborhood of the marked point. The first
coordinate section has a domain local ring; the second coordinate remains
nonzero there. The localization-quotient comparison and colon clearing
turn this into the exact regular-pair input for the incidence calculation.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- Two omitted coordinates force the selected minor to have codimension
at most the ambient dimension minus two. -/
theorem bertini_two_free_coordinates_card_le
    {N c : ℕ} (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (j k : Fin N) (hjk : j ≠ k)
    (hj : j ∉ Set.range cols) (hk : k ∉ Set.range cols) : c + 2 ≤ N := by
  classical
  have hk' : k ∉ Set.range (Fin.cons j cols) := by
    rw [Fin.range_cons, Set.mem_insert_iff, not_or]
    exact ⟨hjk.symm, hk⟩
  have hinj := Fin.cons_injective_of_injective hk'
    (Fin.cons_injective_of_injective hj hcols)
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective (Fin.cons k (Fin.cons j cols)) hinj

/-- The literal coordinate section has the expected principal kernel on
the original affine coordinate ring. -/
theorem coordinateDifference_quotientFactor_ker
    {K : Type*} [Field K] {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (j : Fin N) (a : K) :
    RingHom.ker (Ideal.Quotient.factorₐ K
      (show J ≤ J ⊔ Ideal.span {X j - C a} from le_sup_left)).toRingHom =
      Ideal.span {Ideal.Quotient.mk J (X j - C a)} := by
  change RingHom.ker (Ideal.Quotient.factor
    (show J ≤ J ⊔ Ideal.span {X j - C a} from le_sup_left)) = _
  rw [Ideal.Quotient.factor_ker, Ideal.map_sup, Ideal.map_quotient_self,
    bot_sup_eq, Ideal.map_span, Set.image_singleton]

/-- Two free affine coordinate differences form a regular pair after
shrinking around the marked point. The ring is a principal localization of
the original affine domain, and both elements retain their literal form. -/
theorem exists_principalOpen_regular_coordinate_pair_of_selectedJacobianChart
    {K : Type*} [Field K] {N c : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations))
    (z : Fin N → K) (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    (hminor : aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0)
    (j k : Fin N) (hjk : j ≠ k)
    (hj : j ∉ Set.range cols) (hk : k ∉ Set.range cols) :
    ∃ s : MvPolynomial (Fin N) K ⧸ J,
      affineQuotientRationalPoint J z hz s ≠ 0 ∧
      algebraMap (MvPolynomial (Fin N) K ⧸ J) (Localization.Away s)
        (Ideal.Quotient.mk J (X j - C (z j))) ≠ 0 ∧
      IsRegular (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin N) K ⧸ J) (Localization.Away s)
          (Ideal.Quotient.mk J (X j - C (z j)))})
        (algebraMap (MvPolynomial (Fin N) K ⧸ J) (Localization.Away s)
          (Ideal.Quotient.mk J (X k - C (z k))))) := by
  classical
  letI : J.IsPrime := hJ
  let A := MvPolynomial (Fin N) K ⧸ J
  let J₁ := J ⊔ Ideal.span {X j - C (z j)}
  let B := MvPolynomial (Fin N) K ⧸ J₁
  let a : A := Ideal.Quotient.mk J (X j - C (z j))
  let b : A := Ideal.Quotient.mk J (X k - C (z k))
  let fA := affineQuotientRationalPoint J z hz
  have hz₁ : J₁ ≤ RingHom.ker (aeval z).toRingHom :=
    affinePoint_coordinateDifference_ideal_le_ker J z hz j
  let fB := affineQuotientRationalPoint J₁ z hz₁
  let P := RingHom.ker fA.toRingHom
  let Q := RingHom.ker fB.toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime fA.toRingHom
  letI : Q.IsPrime := RingHom.ker_isPrime fB.toRingHom
  let equations₁ : Fin (c + 1) → MvPolynomial (Fin N) K :=
    Fin.cons (X j - C (z j)) equations
  let cols₁ : Fin (c + 1) → Fin N := Fin.cons j cols
  have hcols₁ : Function.Injective cols₁ := Fin.cons_injective_of_injective hj hcols
  obtain ⟨hIJ₁, hclear₁⟩ := coordinateDifference_local_equations J equations u hIJ hclear j (z j)
  have hminor₁ : aeval z (u * selectedJacobianDeterminant equations₁ cols₁) ≠ 0 := by
    change aeval z (u * selectedJacobianDeterminant
      (Fin.cons (X j - C (z j)) equations) (Fin.cons j cols)) ≠ 0
    rw [selectedJacobianDeterminant_cons_coordinateDifference equations cols j (z j) hj]
    exact hminor
  have hk₁ : k ∉ Set.range cols₁ := by
    change k ∉ Set.range (Fin.cons j cols)
    rw [Fin.range_cons, Set.mem_insert_iff, not_or]
    exact ⟨hjk.symm, hk⟩
  have hcount := bertini_two_free_coordinates_card_le cols hcols j k hjk hj hk
  letI : IsDomain (Localization.AtPrime Q) :=
    isDomain_pointLocalization_of_selectedJacobianChart
      J₁ equations₁ cols₁ hcols₁ u hIJ₁ hclear₁ z hz₁ hminor₁ Q rfl
  have hbLocal := coordinateDifference_ne_zero_pointLocalization
    J₁ equations₁ cols₁ hcols₁ u hIJ₁ hclear₁ z hz₁ hminor₁ k hk₁ (by omega) Q rfl
  let g : A →ₐ[K] B := Ideal.Quotient.factorₐ K (show J ≤ J₁ from le_sup_left)
  have hg : Function.Surjective g := Ideal.Quotient.factor_surjective (show J ≤ J₁ from le_sup_left)
  have hpoints : fB.comp g = fA := by
    apply Ideal.Quotient.algHom_ext
    rfl
  have hPQ : P = Q.comap g := by
    ext x
    change fA x = 0 ↔ fB (g x) = 0
    rw [← AlgHom.comp_apply, hpoints]
  have hker : RingHom.ker g.toRingHom = Ideal.span {a} :=
    coordinateDifference_quotientFactor_ker J j (z j)
  obtain ⟨e, he⟩ := bertini_exists_localization_quotient_equiv
    g hg P Q hPQ (Ideal.span {a}) hker
  letI : IsDomain (Localization.AtPrime P ⧸
      (Ideal.span {a}).map (algebraMap A (Localization.AtPrime P))) :=
    e.injective.isDomain e.toRingHom
  have hbLocal' : Ideal.Quotient.mk
      ((Ideal.span {a}).map (algebraMap A (Localization.AtPrime P)))
      (algebraMap A (Localization.AtPrime P) b) ≠ 0 := by
    intro hzero
    have h := congrArg e hzero
    rw [he b, map_zero] at h
    exact hbLocal h
  have ha : a ≠ 0 := by
    intro ha
    have hmem : X j - C (z j) ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp ha
    apply coordinateDifference_mul_not_mem_of_eval_ne_zero
      J equations cols hcols u hIJ hclear z hz hminor j hj (by omega) 1 (by simp)
    simpa only [one_mul] using hmem
  obtain ⟨s, hs, has, hbs⟩ := bertini_exists_away_regular_pair_of_local_regular
    P a b ha (isRegular_of_ne_zero' hbLocal')
  exact ⟨s, hs, has, hbs⟩

/-- Every integral affine variety of dimension at least two over an
algebraically closed characteristic-zero field has two actual affine
coordinate differences forming a regular pair on a marked principal open. -/
theorem exists_principalOpen_regular_coordinate_pair_of_primeAffine_dimension
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {N r : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ J) = (r : WithBot ℕ∞))
    (hr : 2 ≤ r) :
    ∃ (z : Fin N → K) (hz : J ≤ RingHom.ker (aeval z).toRingHom)
      (j k : Fin N) (s : MvPolynomial (Fin N) K ⧸ J),
      j ≠ k ∧ affineQuotientRationalPoint J z hz s ≠ 0 ∧
      algebraMap (MvPolynomial (Fin N) K ⧸ J) (Localization.Away s)
        (Ideal.Quotient.mk J (X j - C (z j))) ≠ 0 ∧
      IsRegular (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin N) K ⧸ J) (Localization.Away s)
          (Ideal.Quotient.mk J (X j - C (z j)))})
        (algebraMap (MvPolynomial (Fin N) K ⧸ J) (Localization.Away s)
          (Ideal.Quotient.mk J (X k - C (z k))))) := by
  obtain ⟨equations, cols, u, z, j, k, hcols, hjk, hj, hk, hIJ, hclear, hz, hminor⟩ :=
    exists_marked_selectedJacobianChart_two_free_coordinates J hJ hdim hr
  obtain ⟨s, hs, ha, hb⟩ :=
    exists_principalOpen_regular_coordinate_pair_of_selectedJacobianChart
      J hJ equations cols hcols u hIJ hclear z hz hminor j k hjk hj hk
  exact ⟨z, hz, j, k, s, hjk, hs, ha, hb⟩

/-- Retain one common marked point and all its selected Jacobian data
together with the principal regular pair. This joint witness feeds both
the incidence-domain proof and the generic marked-point smoothness proof. -/
theorem exists_marked_selectedJacobianChart_regular_pair
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {N r : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ J) = (r : WithBot ℕ∞))
    (hr : 2 ≤ r) :
    ∃ (equations : Fin (N - r) → MvPolynomial (Fin N) K)
      (cols : Fin (N - r) → Fin N) (u : MvPolynomial (Fin N) K)
      (z : Fin N → K) (hz : J ≤ RingHom.ker (aeval z).toRingHom)
      (j k : Fin N) (s : MvPolynomial (Fin N) K ⧸ J),
      Function.Injective cols ∧ j ≠ k ∧ j ∉ Set.range cols ∧ k ∉ Set.range cols ∧
      Ideal.span (Set.range equations) ≤ J ∧
      (∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations)) ∧
      aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0 ∧
      affineQuotientRationalPoint J z hz s ≠ 0 ∧
      algebraMap (MvPolynomial (Fin N) K ⧸ J) (Localization.Away s)
        (Ideal.Quotient.mk J (X j - C (z j))) ≠ 0 ∧
      IsRegular (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin N) K ⧸ J) (Localization.Away s)
          (Ideal.Quotient.mk J (X j - C (z j)))})
        (algebraMap (MvPolynomial (Fin N) K ⧸ J) (Localization.Away s)
          (Ideal.Quotient.mk J (X k - C (z k))))) := by
  obtain ⟨equations, cols, u, z, j, k, hcols, hjk, hj, hk, hIJ, hclear, hz, hminor⟩ :=
    exists_marked_selectedJacobianChart_two_free_coordinates J hJ hdim hr
  obtain ⟨s, hs, ha, hb⟩ :=
    exists_principalOpen_regular_coordinate_pair_of_selectedJacobianChart
      J hJ equations cols hcols u hIJ hclear z hz hminor j k hjk hj hk
  exact ⟨equations, cols, u, z, hz, j, k, s,
    hcols, hjk, hj, hk, hIJ, hclear, hminor, hs, ha, hb⟩

end
end TranslatedDepthSeven
