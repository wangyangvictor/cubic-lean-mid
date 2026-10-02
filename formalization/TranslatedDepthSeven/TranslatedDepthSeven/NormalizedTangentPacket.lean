import TranslatedDepthSeven.AffineJacobianTransform
import TranslatedDepthSeven.DepthSevenJacobianCertificate
import TranslatedDepthSeven.TangentApplicationConstants
import TranslatedDepthSeven.TangentPacketSpan

/-!
# Tangent packets after the literal affine normalization

This file specializes the elementary tangent-minor argument to the
thirteen-variable, rank-seven situation.  The points below are the normalized
integral variables in `x = x₀ + m y`.  They are required literally to be
common zeros of the original integral equations after applying this affine
map, and to lie in one coordinatewise residue class modulo the displayed
square-free integer `q`.

There are two distinct, and deliberately explicit, conclusions.

* The inequality `7! M^7 < q^8` puts a packet in an affine subspace whose
  direction has dimension at most six.
* The manuscript-scale inequality with `q` of size `T^(5/7)` only proves
  dimension at most nine: it kills the `10 x 10` minors.  No rank-six
  conclusion is silently inferred from that weaker numerical hypothesis.

All Jacobian ranks are ranks of the displayed matrices.  The final theorem
also records how one literal nonzero integral Jacobian minor supplies all of
those ranks after deleting its prime divisors.
-/

namespace TranslatedDepthSeven

noncomputable section

namespace NormalizedTangentPacket

/-- Every member of a finite family belongs to its canonical finite
indexing. -/
theorem indexedFinsetFamily_mem {A : Type*} (S : Finset A) (i : Fin S.card) :
    indexedFinsetFamily S i ∈ S := by
  exact (S.equivFin.symm i).2

/-- Choose the integral quotient of two normalized points which are
coordinatewise congruent modulo `q`. -/
def congruenceQuotient {I : Type*} {N q : ℕ}
    (y : I → IntVector N) (i₀ : I)
    (hcongr : ∀ i, IntVectorCongruent q (y i) (y i₀)) :
    I → IntVector N :=
  fun i ↦ Classical.choose (exists_intVector_rescaling (hcongr i))

theorem congruenceQuotient_spec {I : Type*} {N q : ℕ}
    (y : I → IntVector N) (i₀ : I)
    (hcongr : ∀ i, IntVectorCongruent q (y i) (y i₀))
    (i : I) (j : Fin N) :
    y i j - y i₀ j = (q : ℤ) * congruenceQuotient y i₀ hcongr i j := by
  have h := Classical.choose_spec (exists_intVector_rescaling (hcongr i)) j
  change y i j - y i₀ j =
    (q : ℤ) * Classical.choose
      (exists_intVector_rescaling (hcongr i)) j
  omega

/-- The literal common-zero hypothesis on the original equations becomes
the common-zero hypothesis on their indexed affine transforms. -/
theorem transformed_indexed_commonZero
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x₀ : IntVector 13) (m : ℕ) {I : Type*}
    (y : I → IntVector 13)
    (hzero : ∀ i, IntegralCommonZero equations
      (integralAffineMap x₀ (y i) m)) :
    ∀ i f,
      MvPolynomial.eval (y i)
        (integralAffineTransformFamily x₀ m
          (indexedFinsetFamily equations) f) = 0 := by
  intro i f
  rw [integralAffineTransformFamily, eval_integralAffineTransform]
  exact hzero i _ (indexedFinsetFamily_mem equations f)

/-- Away from prime divisors of the affine scale, rank seven for the
original Jacobian gives rank seven for the normalized Jacobian. -/
theorem transformed_rank_seven
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x₀ y₀ : IntVector 13) (m q : ℕ)
    (hscale : ∀ p, p.Prime → p ∣ q → ¬ p ∣ m)
    (hrank : ∀ p, p.Prime → p ∣ q →
      7 ≤ (jacobianMatrix (indexedFinsetFamily equations)
        (integralAffineMap x₀ y₀ m) p).rank) :
    ∀ p, p.Prime → p ∣ q →
      7 ≤ (jacobianMatrix
        (integralAffineTransformFamily x₀ m
          (indexedFinsetFamily equations)) y₀ p).rank := by
  intro p hp hpq
  rw [jacobianMatrix_transform_rank_eq hp (hscale p hp hpq)]
  exact hrank p hp hpq

/-- A normalized depth-seven packet satisfying the strong `7 x 7` size
inequality lies in a rational affine subspace of direction dimension at most
six. -/
theorem exists_affineSubspace_finrank_le_six
    {I : Type*}
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x₀ : IntVector 13) (m q M : ℕ)
    (y : I → IntVector 13) (i₀ : I)
    (hqpos : 0 < q) (hqsf : Squarefree q)
    (hzero : ∀ i, IntegralCommonZero equations
      (integralAffineMap x₀ (y i) m))
    (hcongr : ∀ i, IntVectorCongruent q (y i) (y i₀))
    (hscale : ∀ p, p.Prime → p ∣ q → ¬ p ∣ m)
    (hrank : ∀ p, p.Prime → p ∣ q →
      7 ≤ (jacobianMatrix (indexedFinsetFamily equations)
        (integralAffineMap x₀ (y i₀) m) p).rank)
    (hcoord : ∀ i j, (y i j - y i₀ j).natAbs ≤ M)
    (hlarge : Nat.factorial 7 * M ^ 7 < q ^ 8) :
    ∃ A : AffineSubspace ℚ (Fin 13 → ℚ),
      Module.finrank ℚ A.direction ≤ 6 ∧
      ∀ i, (fun j ↦ (y i j : ℚ)) ∈ A := by
  let quotient : I → IntVector 13 :=
    congruenceQuotient y i₀ hcongr
  obtain ⟨A, hdim, hmem⟩ :=
    TangentPacketSpan.exists_affineSubspace_of_tangent_packet
      (k := 7) (d := 6) (q := q) (M := M)
      (integralAffineTransformFamily x₀ m
        (indexedFinsetFamily equations))
      y i₀ quotient hqpos hqsf (by omega)
      (transformed_indexed_commonZero equations x₀ m y hzero)
      (by
        intro i j
        exact congruenceQuotient_spec y i₀ hcongr i j)
      (by
        intro p hp hpq
        simpa [jacobianMatrix] using
          transformed_rank_seven equations x₀ (y i₀) m q
            hscale hrank p hp hpq)
      hcoord (by norm_num; exact hlarge)
  exact ⟨A, by omega, hmem⟩

/-- If every normalized coordinate has absolute value at most `2T`, every
coordinate difference has absolute value at most `4T`. -/
theorem coordinateDifference_le_four_mul
    {I : Type*} (y : I → IntVector 13) (i₀ : I) (T : ℕ)
    (hbox : ∀ i j, (y i j).natAbs ≤ 2 * T) :
    ∀ i j,
      (y i j - y i₀ j).natAbs ≤ tangentCoordinateConstant * T := by
  intro i j
  calc
    (y i j - y i₀ j).natAbs ≤
        (y i j).natAbs + (y i₀ j).natAbs := Int.natAbs_sub_le _ _
    _ ≤ 2 * T + 2 * T := Nat.add_le_add (hbox i j) (hbox i₀ j)
    _ = tangentCoordinateConstant * T := by
      simp only [tangentCoordinateConstant]
      omega

/-- At the manuscript surface scale `q ≈ T^(5/7)`, the honest conclusion
is a rational affine subspace of direction dimension at most nine. -/
theorem exists_affineSubspace_finrank_le_nine_of_surface_threshold
    {I : Type*}
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x₀ : IntVector 13) (m q T : ℕ)
    (y : I → IntVector 13) (i₀ : I)
    (hT : 1 ≤ T) (hqpos : 0 < q) (hqsf : Squarefree q)
    (hq : surfaceTangentQThreshold T ≤ q)
    (hzero : ∀ i, IntegralCommonZero equations
      (integralAffineMap x₀ (y i) m))
    (hcongr : ∀ i, IntVectorCongruent q (y i) (y i₀))
    (hscale : ∀ p, p.Prime → p ∣ q → ¬ p ∣ m)
    (hrank : ∀ p, p.Prime → p ∣ q →
      7 ≤ (jacobianMatrix (indexedFinsetFamily equations)
        (integralAffineMap x₀ (y i₀) m) p).rank)
    (hbox : ∀ i j, (y i j).natAbs ≤ 2 * T) :
    ∃ A : AffineSubspace ℚ (Fin 13 → ℚ),
      Module.finrank ℚ A.direction ≤ 9 ∧
      ∀ i, (fun j ↦ (y i j : ℚ)) ∈ A := by
  let quotient : I → IntVector 13 :=
    congruenceQuotient y i₀ hcongr
  obtain ⟨A, hdim, hmem⟩ :=
    TangentPacketSpan.exists_affineSubspace_of_tangent_packet
      (k := 10) (d := 6) (q := q)
      (M := tangentCoordinateConstant * T)
      (integralAffineTransformFamily x₀ m
        (indexedFinsetFamily equations))
      y i₀ quotient hqpos hqsf (by omega)
      (transformed_indexed_commonZero equations x₀ m y hzero)
      (by
        intro i j
        exact congruenceQuotient_spec y i₀ hcongr i j)
      (by
        intro p hp hpq
        simpa [jacobianMatrix] using
          transformed_rank_seven equations x₀ (y i₀) m q
            hscale hrank p hp hpq)
      (coordinateDifference_le_four_mul y i₀ T hbox)
      (surface_tangent_size_inequality_of_nat_bounds hT (le_refl _) hq)
  exact ⟨A, by omega, hmem⟩

/-- One displayed original integral Jacobian minor, coprime to `q`, supplies
the rank hypothesis in the preceding strong packet theorem.  Coprimality of
`q` and `m` is exactly what makes the affine chain-rule scalar invertible at
every prime under consideration. -/
theorem exists_affineSubspace_finrank_le_six_of_coprime_minor
    {I : Type*}
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x₀ : IntVector 13) (m q M : ℕ)
    (y : I → IntVector 13) (i₀ : I)
    (rows : Fin 7 → Fin equations.card) (cols : Fin 7 → Fin 13)
    (hqpos : 0 < q) (hqsf : Squarefree q)
    (hqm : Nat.Coprime q m)
    (hqminor : Nat.Coprime q
      (integralJacobianMinor (indexedFinsetFamily equations)
        (integralAffineMap x₀ (y i₀) m) rows cols).natAbs)
    (hzero : ∀ i, IntegralCommonZero equations
      (integralAffineMap x₀ (y i) m))
    (hcongr : ∀ i, IntVectorCongruent q (y i) (y i₀))
    (hcoord : ∀ i j, (y i j - y i₀ j).natAbs ≤ M)
    (hlarge : Nat.factorial 7 * M ^ 7 < q ^ 8) :
    ∃ A : AffineSubspace ℚ (Fin 13 → ℚ),
      Module.finrank ℚ A.direction ≤ 6 ∧
      ∀ i, (fun j ↦ (y i j : ℚ)) ∈ A := by
  apply exists_affineSubspace_finrank_le_six equations x₀ m q M y i₀
    hqpos hqsf hzero hcongr
  · intro p hp hpq hpm
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpq hpm) hqm
  · exact jacobian_rank_ge_for_prime_divisors_of_coprime_minor
      (indexedFinsetFamily equations)
      (integralAffineMap x₀ (y i₀) m) rows cols hqminor
  · exact hcoord
  · exact hlarge

/-- A rational rank-seven point produces an explicit bounded nonzero
integral certificate.  Once the reservoir modulus is chosen coprime to that
certificate and to the affine scale, the strong packet conclusion follows.
The implication in the conclusion makes the order of these two choices
literal. -/
theorem exists_bounded_certificate_then_affineSubspace_finrank_le_six
    {I : Type*}
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x₀ : IntVector 13) (m q M Y : ℕ)
    (y : I → IntVector 13) (i₀ : I)
    (hqpos : 0 < q) (hqsf : Squarefree q)
    (hregular : IsDepthSevenJacobianRegularAt equations
      (integralAffineMap x₀ (y i₀) m))
    (hx : ∀ j, (integralAffineMap x₀ (y i₀) m j).natAbs ≤ Y)
    (hzero : ∀ i, IntegralCommonZero equations
      (integralAffineMap x₀ (y i) m))
    (hcongr : ∀ i, IntVectorCongruent q (y i) (y i₀))
    (hcoord : ∀ i j, (y i j - y i₀ j).natAbs ≤ M)
    (hlarge : Nat.factorial 7 * M ^ 7 < q ^ 8) :
    ∃ rows : Fin 7 → Fin equations.card,
      ∃ cols : Fin 7 → Fin 13,
        Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor (indexedFinsetFamily equations)
          (integralAffineMap x₀ (y i₀) m) rows cols ≠ 0 ∧
        (integralJacobianMinor (indexedFinsetFamily equations)
          (integralAffineMap x₀ (y i₀) m) rows cols).natAbs ≤
          Nat.factorial 7 *
            (equationFamilySupportBound equations *
              equationFamilyDegreeBound equations *
              equationFamilyCoefficientBound equations *
              max 1 Y ^ equationFamilyDegreeBound equations) ^ 7 ∧
        (Nat.Coprime q m →
          Nat.Coprime q
            (integralJacobianMinor (indexedFinsetFamily equations)
              (integralAffineMap x₀ (y i₀) m) rows cols).natAbs →
          ∃ A : AffineSubspace ℚ (Fin 13 → ℚ),
            Module.finrank ℚ A.direction ≤ 6 ∧
            ∀ i, (fun j ↦ (y i j : ℚ)) ∈ A) := by
  obtain ⟨rows, cols, hrows, hcols, hminor, hbound⟩ :=
    exists_depthSeven_bounded_nonzero_jacobianMinor equations
      (integralAffineMap x₀ (y i₀) m) Y hregular hx
  refine ⟨rows, cols, hrows, hcols, hminor, hbound, ?_⟩
  intro hqm hqminor
  exact exists_affineSubspace_finrank_le_six_of_coprime_minor
    equations x₀ m q M y i₀ rows cols hqpos hqsf hqm hqminor
      hzero hcongr hcoord hlarge

/-- Certificate form of the manuscript-scale conclusion.  This is the
version whose numerical hypothesis is furnished by
`surface_tangent_size_inequality_of_nat_bounds`; its affine subspace has
direction dimension at most nine, not at most six. -/
theorem exists_affineSubspace_finrank_le_nine_of_surface_threshold_of_coprime_minor
    {I : Type*}
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x₀ : IntVector 13) (m q T : ℕ)
    (y : I → IntVector 13) (i₀ : I)
    (rows : Fin 7 → Fin equations.card) (cols : Fin 7 → Fin 13)
    (hT : 1 ≤ T) (hqpos : 0 < q) (hqsf : Squarefree q)
    (hq : surfaceTangentQThreshold T ≤ q)
    (hqm : Nat.Coprime q m)
    (hqminor : Nat.Coprime q
      (integralJacobianMinor (indexedFinsetFamily equations)
        (integralAffineMap x₀ (y i₀) m) rows cols).natAbs)
    (hzero : ∀ i, IntegralCommonZero equations
      (integralAffineMap x₀ (y i) m))
    (hcongr : ∀ i, IntVectorCongruent q (y i) (y i₀))
    (hbox : ∀ i j, (y i j).natAbs ≤ 2 * T) :
    ∃ A : AffineSubspace ℚ (Fin 13 → ℚ),
      Module.finrank ℚ A.direction ≤ 9 ∧
      ∀ i, (fun j ↦ (y i j : ℚ)) ∈ A := by
  apply exists_affineSubspace_finrank_le_nine_of_surface_threshold
    equations x₀ m q T y i₀ hT hqpos hqsf hq hzero hcongr
  · intro p hp hpq hpm
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpq hpm) hqm
  · exact jacobian_rank_ge_for_prime_divisors_of_coprime_minor
      (indexedFinsetFamily equations)
      (integralAffineMap x₀ (y i₀) m) rows cols hqminor
  · exact hbox

/-- A rational rank-seven base point yields a bounded certificate before
the surface-scale reservoir modulus is chosen.  Coprimality with the chosen
minor and the affine scale then gives the actual dimension-nine tangent
packet used in the depth-seven argument. -/
theorem exists_bounded_certificate_then_surface_affineSubspace_finrank_le_nine
    {I : Type*}
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x₀ : IntVector 13) (m q T Y : ℕ)
    (y : I → IntVector 13) (i₀ : I)
    (hT : 1 ≤ T) (hqpos : 0 < q) (hqsf : Squarefree q)
    (hq : surfaceTangentQThreshold T ≤ q)
    (hregular : IsDepthSevenJacobianRegularAt equations
      (integralAffineMap x₀ (y i₀) m))
    (hx : ∀ j, (integralAffineMap x₀ (y i₀) m j).natAbs ≤ Y)
    (hzero : ∀ i, IntegralCommonZero equations
      (integralAffineMap x₀ (y i) m))
    (hcongr : ∀ i, IntVectorCongruent q (y i) (y i₀))
    (hbox : ∀ i j, (y i j).natAbs ≤ 2 * T) :
    ∃ rows : Fin 7 → Fin equations.card,
      ∃ cols : Fin 7 → Fin 13,
        Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor (indexedFinsetFamily equations)
          (integralAffineMap x₀ (y i₀) m) rows cols ≠ 0 ∧
        (integralJacobianMinor (indexedFinsetFamily equations)
          (integralAffineMap x₀ (y i₀) m) rows cols).natAbs ≤
          Nat.factorial 7 *
            (equationFamilySupportBound equations *
              equationFamilyDegreeBound equations *
              equationFamilyCoefficientBound equations *
              max 1 Y ^ equationFamilyDegreeBound equations) ^ 7 ∧
        (Nat.Coprime q m →
          Nat.Coprime q
            (integralJacobianMinor (indexedFinsetFamily equations)
              (integralAffineMap x₀ (y i₀) m) rows cols).natAbs →
          ∃ A : AffineSubspace ℚ (Fin 13 → ℚ),
            Module.finrank ℚ A.direction ≤ 9 ∧
            ∀ i, (fun j ↦ (y i j : ℚ)) ∈ A) := by
  obtain ⟨rows, cols, hrows, hcols, hminor, hbound⟩ :=
    exists_depthSeven_bounded_nonzero_jacobianMinor equations
      (integralAffineMap x₀ (y i₀) m) Y hregular hx
  refine ⟨rows, cols, hrows, hcols, hminor, hbound, ?_⟩
  intro hqm hqminor
  exact
    exists_affineSubspace_finrank_le_nine_of_surface_threshold_of_coprime_minor
      equations x₀ m q T y i₀ rows cols hT hqpos hqsf hq hqm hqminor
        hzero hcongr hbox

end NormalizedTangentPacket

end

end TranslatedDepthSeven
