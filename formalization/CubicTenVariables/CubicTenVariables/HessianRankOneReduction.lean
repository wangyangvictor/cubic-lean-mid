import CubicTenVariables.IntegralOriginCertificate
import HessianTheorem11.UnconditionalResults
import HessianTheorem11.MatrixRankMinors

/-! All-prime boundedness of the actual rank-at-most-one stratum on an
integral anisotropic cubic. A Nullstellensatz certificate is cleared over
Z, so the exceptional primes and the uniform constant precede the prime. -/
noncomputable section
namespace CubicTenVariables.HessianRankOneReduction
open MvPolynomial HessianTheorem11
open IntegralOriginCertificate

/-- All minors of order greater than one. Repeated row and column choices
are harmless and allow a direct exact rank criterion. -/
def largeMinors {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) : Set (MvPolynomial (Fin n) R) :=
  {f | ∃ (k : ℕ), 1 < k ∧ ∃ (rows cols : Fin k → Fin n),
    f = ((hessianPolynomial F).submatrix rows cols).det}

/-- The actual ideal cutting out F=0 and Hessian rank at most one. -/
def rankOneIdeal {n : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    Ideal (MvPolynomial (Fin n) ℤ) := Ideal.span (insert F (largeMinors F))

theorem eval₂_minor {R K : Type*} [CommRing R] [CommRing K] {n k : ℕ}
    (F : MvPolynomial (Fin n) R) (f : R →+* K) (x : Fin n → K)
    (rows cols : Fin k → Fin n) :
    eval₂ f x ((hessianPolynomial F).submatrix rows cols).det =
      ((hessian (map f F) x).submatrix rows cols).det := by
  change (eval₂Hom f x) ((hessianPolynomial F).submatrix rows cols).det = _
  rw [(eval₂Hom f x).map_det]
  congr 1
  ext i j
  simp [hessian, hessianPolynomial, pderiv_map, eval_map]

theorem zero_of_rankOneIdeal {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    {K : Type*} [Field K] (f : ℤ →+* K) (x : Fin n → K)
    (hx : ∀ g ∈ rankOneIdeal F, eval₂ f x g = 0) :
    eval₂ f x F = 0 ∧ (hessian (map f F) x).rank ≤ 1 := by
  constructor
  · exact hx _ (Ideal.subset_span (Set.mem_insert F _))
  · apply MatrixRankMinors.rank_le_of_minors_vanish
    intro k hk rows cols
    rw [← eval₂_minor]
    exact hx _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, hk, rows, cols, rfl⟩))

theorem rankOneIdeal_vanishes {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    {K : Type*} [Field K] (f : ℤ →+* K) (x : Fin n → K)
    (hF : eval₂ f x F = 0) (hr : (hessian (map f F) x).rank ≤ 1) :
    ∀ g ∈ rankOneIdeal F, eval₂ f x g = 0 := by
  have hle : rankOneIdeal F ≤ RingHom.ker (eval₂Hom f x) := by
    apply Ideal.span_le.mpr
    intro g hg
    rcases hg with rfl | ⟨k, hk, rows, cols, rfl⟩
    · exact hF
    · change eval₂ f x _ = 0
      rw [eval₂_minor]
      by_contra hd
      have he := MatrixRankMinors.minor_size_le_rank (hessian (map f F) x) rows cols hd
      omega
  exact fun g hg => hle hg

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The previously proved characteristic-zero rank-one theorem supplies the
literal geometric zero-locus hypothesis for the integral ideal. -/
theorem geometric_origin_locus {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    zeroLocus GeometricField (rationalIdeal (rankOneIdeal F)) ⊆ {0} := by
  intro x hx
  by_cases hn : 0 < n
  · have hz : ∀ g ∈ rankOneIdeal F,
        eval₂ (Int.castRingHom GeometricField) x g = 0 := by
      intro g hg
      have h := hx _ (Ideal.mem_map_of_mem
        (algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ)) hg)
      simpa [MvPolynomial.algebraMap_def, aeval_def, eval₂_map] using h
    obtain ⟨hzero, hrank⟩ := zero_of_rankOneIdeal F (Int.castRingHom GeometricField) x hz
    let Q : AnisotropicCubic n := ⟨map (Int.castRingHom ℚ) F, hF.map _, hA⟩
    have he := BibleLowRank.anisotropic_on_cubic_rank_one_eq_origin
      provedSymmetricDeterminantalTangent Q hn
    apply he.subset
    change eval x (geometricPolynomial Q.polynomial) = 0 ∧
      (hessian (geometricPolynomial Q.polynomial) x).rank ≤ 1
    have hmap : geometricPolynomial Q.polynomial = map (Int.castRingHom GeometricField) F := by
      simp only [Q, geometricPolynomial, map_map]
      congr 1
    rw [hmap]
    exact ⟨by simpa [eval_map] using hzero, hrank⟩
  · have hn0 : n = 0 := by omega
    subst n
    exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)

/-- A single nonzero integer excludes nonzero on-cubic rank-one points at
every prime not dividing it. -/
theorem exists_good_prime_certificate {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ¬ (p : ℤ) ∣ D → ∀ x : Fin n → ZMod p,
        eval x (map (Int.castRingHom (ZMod p)) F) = 0 →
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank ≤ 1 → x = 0 := by
  obtain ⟨D, hd, hgood⟩ := IntegralOriginCertificate.exists_good_prime_certificate
    (rankOneIdeal F) (geometric_origin_locus F hF hA)
  refine ⟨D, hd, ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro hprime x hx hr
  apply hgood p hp hprime x
  apply rankOneIdeal_vanishes F (Int.castRingHom (ZMod p)) x
  · simpa [eval_map] using hx
  · exact hr

/-- Literal points on the reduced cubic with actual Hessian rank at most one. -/
def onCubicRankOnePoints {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] : Finset (Fin n → ZMod p) := by
  classical
  exact Finset.univ.filter (fun x =>
    eval x (map (Int.castRingHom (ZMod p)) F) = 0 ∧
      (hessian (map (Int.castRingHom (ZMod p)) F) x).rank ≤ 1)

/-- A fixed positive constant bounds the literal rank-at-most-one zero
stratum at every prime, including primes of bad reduction and 2 or 3. -/
theorem exists_uniform_onCubic_rankOne_bound {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      (onCubicRankOnePoints F p).card ≤ C := by
  classical
  obtain ⟨D, hd, hgood⟩ := exists_good_prime_certificate F hF hA
  refine ⟨max 1 (D.natAbs ^ n), lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hpd : (p : ℤ) ∣ D
  · have hple : p ≤ D.natAbs := by
      simpa only [Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero hpd hd
    calc
      _ ≤ Fintype.card (Fin n → ZMod p) := Finset.card_le_univ _
      _ = p ^ n := by simp [ZMod.card]
      _ ≤ D.natAbs ^ n := Nat.pow_le_pow_left hple n
      _ ≤ _ := le_max_right _ _
  · have hsub : onCubicRankOnePoints F p ⊆ {0} := by
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      exact Finset.mem_singleton.mpr (hgood p hp hpd x h.1 h.2)
    calc
      _ ≤ ({0} : Finset (Fin n → ZMod p)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
      _ ≤ _ := le_max_left _ _

/-- In particular the exact rank-one stratum has exponent delta(1)=0.
The single constant is chosen before both the prime and the rank label. -/
theorem exists_uniform_onCubic_low_rank_bound {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ r : ℕ, r ≤ 1 →
        ((Finset.univ : Finset (Fin n → ZMod p)).filter (fun x =>
          eval x (map (Int.castRingHom (ZMod p)) F) = 0 ∧
          (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = r)).card ≤ C := by
  classical
  obtain ⟨C, hc, hC⟩ := exists_uniform_onCubic_rankOne_bound F hF hA
  refine ⟨C, hc, ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro r hr
  refine le_trans (Finset.card_le_card ?_) (hC p hp)
  intro x hx
  obtain ⟨hx0, hxr⟩ := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hx0, hxr.le.trans hr⟩

end CubicTenVariables.HessianRankOneReduction
