import CubicTenVariables.SecondLiftSum

/-!
# Exact higher terminal splitting

At a positive modulus `M*L`, when `M` divides the integral cubic coefficient
`A`, split the actual representatives as `v + L*x`. The cubic contribution
is constant on each block. The inner sum is the literal quadratic sum
modulo `M`, with linear coefficient `ell + alpha*H_F(y)*v` and quadratic
coefficient `alpha*L`. The constant character is retained in the exact
identity and has norm one in the resulting triangle inequality.

This part uses no oddness, unit, Smith-profile or analytic premise.
-/

noncomputable section
namespace CubicTenVariables.TerminalHighSplit

open MvPolynomial HessianTheorem11 CubicTaylorExpansion TerminalCubicSum
open LiftingCharacters PrimeSumAdapter SecondLiftPhase SecondLiftSum MixedRadixLifting
open scoped BigOperators

/-- The actual quadratic inner phase, before any reduction. -/
def quadraticInnerPhase {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (L alpha : R) (ell y v x : Fin n → R) : R :=
  dotProduct (ell + alpha • (hessian F y).mulVec v) x +
    alpha * L * quadraticAt F y x

/-- The integral quadratic term scales by the square. Cancellation here is
only in the integer coefficient identity, before reduction at any prime. -/
theorem quadraticAt_smul_int {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (y x : Fin n → ℤ) (L : ℤ) :
    quadraticAt F y (L • x) = L^2 * quadraticAt F y x := by
  apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide)
  calc
    2 * quadraticAt F y (L • x) =
        dotProduct (L • x) ((hessian F y).mulVec (L • x)) :=
      two_mul_quadraticAt F hF y (L • x)
    _ = L^2 * dotProduct x ((hessian F y).mulVec x) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
      simp only [smul_eq_mul]
      ring
    _ = 2 * (L^2 * quadraticAt F y x) := by
      rw [← two_mul_quadraticAt F hF]
      ring

/-- Symmetry puts the Hessian cross term in the manuscript's linear coefficient. -/
theorem quadraticAt_add_smul_int {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (y v x : Fin n → ℤ) (L : ℤ) :
    quadraticAt F y (v + L • x) = quadraticAt F y v +
      L * dotProduct ((hessian F y).mulVec v) x + L^2 * quadraticAt F y x := by
  rw [quadraticAt_add F hF, quadraticAt_smul_int F hF,
    Matrix.mulVec_smul, dotProduct_smul]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hessian_symmetric F y]
  simp only [smul_eq_mul]
  ring

/-- The complete integral phase difference, including the multiple which
will disappear modulo `M*L` when `M` divides `A`. -/
theorem terminalPhase_highSplit {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A L alpha : ℤ) (ell y v x : Fin n → ℤ) :
    terminalPhase F A ell alpha y (v + L • x) =
      terminalPhase F A ell alpha y v +
        L * quadraticInnerPhase F L alpha ell y v x +
        alpha*A*L*(directional F v x + L*quadraticAt F v x + L^2*eval x F) := by
  unfold terminalPhase quadraticInnerPhase
  rw [quadraticAt_add_smul_int F hF, eval_cubic_add_smul F hF]
  simp only [dotProduct_add, dotProduct_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

/-- Exact normalized character factorization at arbitrary positive split moduli. -/
theorem residueExponential_highSplit {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (M L : ℕ) [NeZero M] [NeZero L]
    (A alpha : ℤ) (hMA : (M : ℤ) ∣ A) (ell y v x : Fin n → ℤ) :
    residueExponential (M*L) (terminalPhase F A ell alpha y (v + (L:ℤ) • x)) =
      residueExponential (M*L) (terminalPhase F A ell alpha y v) *
        residueExponential M (quadraticInnerPhase F (L:ℤ) alpha ell y v x) := by
  calc
    _ = residueExponential (M*L) (terminalPhase F A ell alpha y v +
        (L:ℤ) * quadraticInnerPhase F (L:ℤ) alpha ell y v x) := by
      apply residueExponential_eq_of_cast_eq
      have hz : ((alpha*A*(L:ℤ)*(directional F v x + (L:ℤ)*quadraticAt F v x +
          (L:ℤ)^2*eval x F) : ℤ) : ZMod (M*L)) = 0 := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        obtain ⟨k, rfl⟩ := hMA
        refine ⟨alpha*k*(directional F v x + (L:ℤ)*quadraticAt F v x +
          (L:ℤ)^2*eval x F), ?_⟩
        push_cast
        ring
      rw [terminalPhase_highSplit F hF, Int.cast_add, hz, add_zero]
    _ = _ := by
      rw [residueExponential_add, residueExponential_mul_modulus]

/-- The literal residue-ring quadratic sum left after the higher split. -/
def quadraticInnerSum (M : ℕ) [NeZero M] {n : ℕ}
    (F : MvPolynomial (Fin n) (ZMod M)) (L alpha : ZMod M)
    (ell y v : Fin n → ZMod M) : ℂ :=
  ∑ x : Fin n → ZMod M, ZMod.stdAddChar (quadraticInnerPhase F L alpha ell y v x)

/-- Every coefficient, coordinate, Hessian entry and partial is reduced by
its actual integer ring homomorphism. -/
theorem quadraticInnerPhase_intCast {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (M : ℕ) (L alpha : ℤ) (ell y v x : Fin n → ℤ) :
    ((quadraticInnerPhase F L alpha ell y v x : ℤ) : ZMod M) =
      quadraticInnerPhase (map (Int.castRingHom (ZMod M)) F) (L : ZMod M)
        (alpha : ZMod M) (fun i => (ell i : ZMod M)) (fun i => (y i : ZMod M))
        (fun i => (v i : ZMod M)) (fun i => (x i : ZMod M)) := by
  simp only [quadraticInnerPhase, quadraticAt, directional, dotProduct, gradient,
    hessian, hessianPolynomial, Matrix.mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    pderiv_map, Int.cast_add, Int.cast_mul, Int.cast_sum, cast_eval_int]

/-- Exact conversion of the original terminal sum to canonical finite
integer representatives, with the positive `2πi` convention unchanged. -/
theorem terminalSum_eq_integer_representatives {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (q : ℕ) [NeZero q]
    (A alpha : ℤ) (ell y : Fin n → ℤ) :
    terminalSum q (map (Int.castRingHom (ZMod q)) F) (A : ZMod q)
      (fun i => (ell i : ZMod q)) (alpha : ZMod q) (fun i => (y i : ZMod q)) =
      ∑ z : Fin n → Fin q,
        residueExponential q (terminalPhase F A ell alpha y (integerVector z)) := by
  symm
  unfold terminalSum
  apply Fintype.sum_equiv (vectorResidueEquiv q n)
  intro z
  rw [residueExponential_eq_stdAddChar, terminalPhase_intCast]
  simp only [vectorResidueEquiv_apply, integerVector, Int.cast_natCast]

/-- The inner integer sum is the actual lower-modulus residue sum. -/
theorem sum_quadraticInner_integer_representatives {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (M L : ℕ) [NeZero M]
    (alpha : ℤ) (ell y v : Fin n → ℤ) :
    (∑ x : Fin n → Fin M,
      residueExponential M (quadraticInnerPhase F (L:ℤ) alpha ell y v (integerVector x))) =
      quadraticInnerSum M (map (Int.castRingHom (ZMod M)) F) (L : ZMod M)
        (alpha : ZMod M) (fun i => (ell i : ZMod M)) (fun i => (y i : ZMod M))
        (fun i => (v i : ZMod M)) := by
  unfold quadraticInnerSum
  apply Fintype.sum_equiv (vectorResidueEquiv M n)
  intro x
  rw [residueExponential_eq_stdAddChar, quadraticInnerPhase_intCast]
  simp only [vectorResidueEquiv_apply, integerVector, Int.cast_natCast]

/-- Exact higher terminal splitting at `M*L`, retaining the constant phase.
The outer representatives are genuinely modulo `L`, not mapped from that
residue ring into an unrelated ring. -/
theorem terminalSum_highSplit {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (M L : ℕ) [NeZero M] [NeZero L]
    (A alpha : ℤ) (hMA : (M : ℤ) ∣ A) (ell y : Fin n → ℤ) :
    terminalSum (M*L) (map (Int.castRingHom (ZMod (M*L))) F) (A : ZMod (M*L))
      (fun i => (ell i : ZMod (M*L))) (alpha : ZMod (M*L))
      (fun i => (y i : ZMod (M*L))) =
      ∑ v : Fin n → Fin L,
        residueExponential (M*L) (terminalPhase F A ell alpha y (integerVector v)) *
          quadraticInnerSum M (map (Int.castRingHom (ZMod M)) F) (L : ZMod M)
            (alpha : ZMod M) (fun i => (ell i : ZMod M)) (fun i => (y i : ZMod M))
            (fun i => ((v i).val : ZMod M)) := by
  rw [terminalSum_eq_integer_representatives, sum_mixedRadixVector]
  apply Finset.sum_congr rfl
  intro v _
  have hvec (x : Fin n → Fin M) :
      integerVector (mixedRadixVectorEquiv n M L (v,x)) =
        integerVector v + (L:ℤ) • integerVector x :=
    mixedRadixVectorEquiv_intCast n M L v x
  simp_rw [hvec, residueExponential_highSplit F hF M L A alpha hMA]
  rw [← Finset.mul_sum, sum_quadraticInner_integer_representatives]
  simp only [integerVector, Int.cast_natCast]

/-- The source's triangle-inequality bound, with the literal quadratic
inner sums and without an odd-prime hypothesis. -/
theorem norm_terminalSum_highSplit_le {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (M L : ℕ) [NeZero M] [NeZero L]
    (A alpha : ℤ) (hMA : (M : ℤ) ∣ A) (ell y : Fin n → ℤ) :
    ‖terminalSum (M*L) (map (Int.castRingHom (ZMod (M*L))) F) (A : ZMod (M*L))
      (fun i => (ell i : ZMod (M*L))) (alpha : ZMod (M*L))
      (fun i => (y i : ZMod (M*L)))‖ ≤
      ∑ v : Fin n → Fin L,
        ‖quadraticInnerSum M (map (Int.castRingHom (ZMod M)) F) (L : ZMod M)
          (alpha : ZMod M) (fun i => (ell i : ZMod M)) (fun i => (y i : ZMod M))
          (fun i => ((v i).val : ZMod M))‖ := by
  rw [terminalSum_highSplit F hF M L A alpha hMA]
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro v _
  rw [norm_mul, norm_residueExponential, one_mul]

/-- Changing only the displayed modulus equality preserves the actual
canonical integer representatives in a finite vector sum. -/
theorem sum_integerVector_finCongr {S : Type*} [AddCommMonoid S]
    (n q q' : ℕ) (h : q = q') (f : (Fin n → ℤ) → S) :
    (∑ x : Fin n → Fin q, f (integerVector x)) =
      ∑ x : Fin n → Fin q', f (integerVector x) := by
  apply Fintype.sum_equiv (Equiv.piCongrRight fun _ : Fin n => finCongr h)
  intro x
  rfl

/-- The exact prime-power identity. The stronger boundary case `a = t`
is included; the manuscript uses `a < t`. Primality is not needed here. -/
theorem terminalSum_primePower_highSplit {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p a t : ℕ) [NeZero p] (hat : a ≤ t)
    (A alpha : ℤ) (hA : ((p^a : ℕ) : ℤ) ∣ A) (ell y : Fin n → ℤ) :
    terminalSum (p^t) (map (Int.castRingHom (ZMod (p^t))) F) (A : ZMod (p^t))
      (fun i => (ell i : ZMod (p^t))) (alpha : ZMod (p^t))
      (fun i => (y i : ZMod (p^t))) =
      ∑ v : Fin n → Fin (p^(t-a)),
        residueExponential (p^t) (terminalPhase F A ell alpha y (integerVector v)) *
          quadraticInnerSum (p^a) (map (Int.castRingHom (ZMod (p^a))) F)
            ((p^(t-a) : ℕ) : ZMod (p^a)) (alpha : ZMod (p^a))
            (fun i => (ell i : ZMod (p^a))) (fun i => (y i : ZMod (p^a)))
            (fun i => ((v i).val : ZMod (p^a))) := by
  have hmod : p^a * p^(t-a) = p^t := by rw [← pow_add, Nat.add_sub_of_le hat]
  rw [terminalSum_eq_integer_representatives]
  have h := terminalSum_highSplit F hF (p^a) (p^(t-a)) A alpha hA ell y
  rw [terminalSum_eq_integer_representatives] at h
  simp only [hmod] at h
  rw [sum_integerVector_finCongr n _ _ hmod
    (fun z => residueExponential (p^t) (terminalPhase F A ell alpha y z))] at h
  exact h

/-- The literal bound for `z = v + p^(t-a)*x`; no oddness or unit hypothesis. -/
theorem norm_terminalSum_primePower_highSplit_le {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p a t : ℕ) [NeZero p] (hat : a ≤ t)
    (A alpha : ℤ) (hA : ((p^a : ℕ) : ℤ) ∣ A) (ell y : Fin n → ℤ) :
    ‖terminalSum (p^t) (map (Int.castRingHom (ZMod (p^t))) F) (A : ZMod (p^t))
      (fun i => (ell i : ZMod (p^t))) (alpha : ZMod (p^t))
      (fun i => (y i : ZMod (p^t)))‖ ≤
      ∑ v : Fin n → Fin (p^(t-a)),
        ‖quadraticInnerSum (p^a) (map (Int.castRingHom (ZMod (p^a))) F)
          ((p^(t-a) : ℕ) : ZMod (p^a)) (alpha : ZMod (p^a))
          (fun i => (ell i : ZMod (p^a))) (fun i => (y i : ZMod (p^a)))
          (fun i => ((v i).val : ZMod (p^a)))‖ := by
  have hmod : p^a * p^(t-a) = p^t := by rw [← pow_add, Nat.add_sub_of_le hat]
  rw [terminalSum_eq_integer_representatives]
  have h := norm_terminalSum_highSplit_le F hF (p^a) (p^(t-a)) A alpha hA ell y
  rw [terminalSum_eq_integer_representatives] at h
  simp only [hmod] at h
  rw [sum_integerVector_finCongr n _ _ hmod
    (fun z => residueExponential (p^t) (terminalPhase F A ell alpha y z))] at h
  exact h

/-- Arbitrary original residue parameters, with their canonical integer
representatives used only for actual reduction to the inner modulus. -/
theorem norm_terminalSum_primePower_highSplit_le_residue {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (p a t : ℕ) [NeZero p] (hat : a ≤ t)
    (A : ℤ) (hA : ((p^a : ℕ) : ℤ) ∣ A)
    (alpha : ZMod (p^t)) (ell y : Fin n → ZMod (p^t)) :
    ‖terminalSum (p^t) (map (Int.castRingHom (ZMod (p^t))) F)
      (A : ZMod (p^t)) ell alpha y‖ ≤
      ∑ v : Fin n → Fin (p^(t-a)),
        ‖quadraticInnerSum (p^a) (map (Int.castRingHom (ZMod (p^a))) F)
          ((p^(t-a) : ℕ) : ZMod (p^a)) (alpha.val : ZMod (p^a))
          (fun i => ((ell i).val : ZMod (p^a)))
          (fun i => ((y i).val : ZMod (p^a)))
          (fun i => ((v i).val : ZMod (p^a)))‖ := by
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
    norm_terminalSum_primePower_highSplit_le F hF p a t hat A (alpha.val : ℤ) hA
      (fun i => ((ell i).val : ℤ)) (fun i => ((y i).val : ℤ))

end CubicTenVariables.TerminalHighSplit
