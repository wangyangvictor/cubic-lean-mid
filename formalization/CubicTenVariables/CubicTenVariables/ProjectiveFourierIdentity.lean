import CubicTenVariables.PrimeScalarAveraging
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! Exact finite-field cone/projective Fourier identity on actual projective
quotient points. No point-count estimate, cohomology or literature input is
used. The field may be any finite field, not only a prime field. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.ProjectiveFourierIdentity
open MvPolynomial FiniteFieldFourier
open scoped BigOperators

variable {k : Type*} [Field k] [Fintype k] {n d : ℕ}

/-- The actual projective zero points, using the quotient by nonzero scalar
multiples. Homogeneity makes the predicate independent of the representative. -/
def zeroPoints (F : MvPolynomial (Fin n) k) :=
  {p : Projectivization k (Fin n → k) // eval p.rep F = 0}

/-- Actual projective points of the hyperplane section. -/
def sectionPoints (F : MvPolynomial (Fin n) k) (v : Fin n → k) :=
  {p : Projectivization k (Fin n → k) // eval p.rep F = 0 ∧ dotProduct v p.rep = 0}

/-- Cardinality of an actual cone obtained from its projective quotient.
The scalar invariance and inclusion of the origin are proved at applications. -/
theorem cone_card (P : (Fin n → k) → Prop) (h0 : P 0)
    (hsmul : ∀ (a : k), a ≠ 0 → ∀ x, P (a • x) ↔ P x) :
    Nat.card {x : Fin n → k // P x} =
      Nat.card {p : Projectivization k (Fin n → k) // P p.rep} *
        (Fintype.card k - 1) + 1 := by
  classical
  let Q := {p : Projectivization k (Fin n → k) // P p.rep}
  let A := {x : Fin n → k // x ≠ 0 ∧ P x}
  let f : Q × kˣ → A := fun z =>
    ⟨(z.2 : k) • z.1.val.rep,
      smul_ne_zero z.2.ne_zero z.1.val.rep_nonzero,
      (hsmul z.2 z.2.ne_zero _).mpr z.1.property⟩
  have hmk (z : Q × kˣ) :
      Projectivization.mk k (f z).val (f z).property.1 = z.1.val := by
    rw [← z.1.val.mk_rep]
    exact (Projectivization.mk_eq_mk_iff k _ _ _ _).mpr ⟨z.2, rfl⟩
  have hinj : Function.Injective f := by
    rintro ⟨p,a⟩ ⟨q,b⟩ h
    have hp : p = q := Subtype.ext (by
      have hh := congrArg (fun x : A => Projectivization.mk k x.val x.property.1) h
      simpa only [hmk] using hh)
    subst q
    have hs : (a : k) • p.val.rep = (b : k) • p.val.rep := congrArg Subtype.val h
    have hab : a = b := Units.ext (smul_left_injective k p.val.rep_nonzero hs)
    subst b
    rfl
  have hsurj : Function.Surjective f := by
    intro x
    let p : Projectivization k (Fin n → k) := Projectivization.mk k x.val x.property.1
    obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep k x.val x.property.1
    have hp : P p.rep := by
      change P (Projectivization.mk k x.val x.property.1).rep
      rw [← ha]
      exact (hsmul a a.ne_zero x.val).mpr x.property.2
    refine ⟨(⟨p,hp⟩,a⁻¹),Subtype.ext ?_⟩
    change ((a⁻¹ : kˣ) : k) • p.rep = x.val
    change ((a⁻¹ : kˣ) : k) • (Projectivization.mk k x.val x.property.1).rep = x.val
    rw [← ha]
    simp only [Units.smul_def, smul_smul, Units.inv_mul, one_smul]
  have hnonzero : Nat.card A = Nat.card Q * (Fintype.card k - 1) := by
    rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩),Nat.card_prod]
    simp only [Nat.card_eq_fintype_card,Fintype.card_units]
  have hcount : Nat.card {x : Fin n → k // P x} = Nat.card A + 1 := by
    have h := Finset.card_erase_add_one (s := Finset.univ.filter P) (a := 0)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h0⟩)
    have he : (Finset.univ.filter P).erase 0 =
        Finset.univ.filter (fun x : Fin n → k => x ≠ 0 ∧ P x) := by
      ext x
      simp [and_comm]
    rw [he] at h
    simpa only [A,Nat.card_eq_fintype_card,Fintype.card_subtype] using h.symm
  rw [hcount,hnonzero]

omit [Fintype k] in
/-- Homogeneity preserves the literal zero predicate under every nonzero
scalar, over any characteristic. -/
theorem eval_smul_zero_iff (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous d)
    (a : k) (ha : a ≠ 0) (x : Fin n → k) :
    eval (a • x) F = 0 ↔ eval x F = 0 := by
  have h := CubicGradientScaling.homogeneous_eval₂_smul F hF (RingHom.id k) x a
  simp only [eval₂_id] at h
  rw [h,mul_eq_zero]
  simp [pow_ne_zero d ha]

omit [Fintype k] in
theorem eval_origin_zero (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous d)
    (hd : 0 < d) : eval (0 : Fin n → k) F = 0 := by
  have h := CubicGradientScaling.homogeneous_eval₂_smul F hF
    (RingHom.id k) (0 : Fin n → k) (0 : k)
  simpa only [zero_smul,eval₂_id,zero_pow hd.ne',zero_mul] using h

omit [Fintype k] in
/-- The representative definition is exactly the homogeneous zero locus
on quotient projective points, not a choice-dependent substitute. -/
theorem zero_mk_iff (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous d)
    (x : Fin n → k) (hx : x ≠ 0) :
    eval (Projectivization.mk k x hx).rep F = 0 ↔ eval x F = 0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep k x hx
  rw [← ha]
  exact eval_smul_zero_iff F hF a a.ne_zero x

omit [Fintype k] in
theorem section_mk_iff (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous d)
    (v x : Fin n → k) (hx : x ≠ 0) :
    (eval (Projectivization.mk k x hx).rep F = 0 ∧
      dotProduct v (Projectivization.mk k x hx).rep = 0) ↔
      eval x F = 0 ∧ dotProduct v x = 0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep k x hx
  rw [← ha]
  simp only [Units.smul_def,eval_smul_zero_iff F hF a a.ne_zero,
    dotProduct_smul,smul_eq_mul,mul_eq_zero,a.ne_zero,false_or]

/-- The cardinality of the actual affine zero cone, including its vertex. -/
theorem affine_zero_card (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous d)
    (hd : 0 < d) :
    Nat.card {x : Fin n → k // eval x F = 0} =
      Nat.card (zeroPoints F) * (Fintype.card k - 1) + 1 :=
  cone_card (fun x => eval x F = 0) (eval_origin_zero F hF hd)
    (eval_smul_zero_iff F hF)

/-- The same exact conversion for every hyperplane section, including the
degenerate frequency zero. -/
theorem affine_section_card (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous d)
    (hd : 0 < d) (v : Fin n → k) :
    Nat.card {x : Fin n → k // eval x F = 0 ∧ dotProduct v x = 0} =
      Nat.card (sectionPoints F v) * (Fintype.card k - 1) + 1 := by
  apply cone_card (fun x => eval x F = 0 ∧ dotProduct v x = 0)
  · exact ⟨eval_origin_zero F hF hd,by simp⟩
  · intro a ha x
    simp only [eval_smul_zero_iff F hF a ha,dotProduct_smul,
      smul_eq_mul,mul_eq_zero,ha,false_or]

/-- Literal Fourier sum over a homogeneous affine cone expressed using
actual projective point counts. The formula is valid even at frequency zero. -/
theorem zeroFiberSum_eq_projective_counts (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (v : Fin n → k) :
    zeroFiberSum ψ F v = 1 + (Fintype.card k : ℂ) *
      (Nat.card (sectionPoints F v) : ℂ) - (Nat.card (zeroPoints F) : ℂ) := by
  classical
  have hcard : 1 ≤ Fintype.card k := Fintype.card_pos
  have hq : (Fintype.card k : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card k).ne'
  have hX := congrArg (fun m : ℕ => (m : ℂ)) (affine_zero_card F hF hd)
  have hH := congrArg (fun m : ℕ => (m : ℂ)) (affine_section_card F hF hd v)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hcard,Nat.cast_one] at hX hH
  have h := PrimeScalarAveraging.scalar_average ψ hψ F hF v
  rw [hX,hH] at h
  apply mul_left_cancel₀ hq
  linear_combination h

/-- The manuscript's T includes subtraction of the zero-frequency main
term; extension fields here are fields, not prime-power residue rings. -/
def normalizedFourierSum (ψ : AddChar k ℂ) (F : MvPolynomial (Fin n) k)
    (v : Fin n → k) : ℂ := by
  classical
  exact zeroFiberSum ψ F v - if v = 0 then (Fintype.card k : ℂ)^(n-1) else 0

/-- Exact n10:T normalization and projective identity at every nonzero
frequency, over every finite field and every nontrivial additive character. -/
theorem normalizedFourierSum_eq_projective_counts (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (v : Fin n → k) (hv : v ≠ 0) :
    normalizedFourierSum ψ F v = 1 + (Fintype.card k : ℂ) *
      (Nat.card (sectionPoints F v) : ℂ) - (Nat.card (zeroPoints F) : ℂ) := by
  simpa only [normalizedFourierSum,if_neg hv,sub_zero] using
    zeroFiberSum_eq_projective_counts ψ hψ F hF hd v

/-- Numerical character independence follows from the actual count identity.
This asserts no isomorphism, lissity or constructibility of Fourier sheaves. -/
theorem normalizedFourierSum_character_independent
    (ψ χ : AddChar k ℂ) (hψ : ψ ≠ 1) (hχ : χ ≠ 1)
    (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (v : Fin n → k) (hv : v ≠ 0) :
    normalizedFourierSum ψ F v = normalizedFourierSum χ F v := by
  rw [normalizedFourierSum_eq_projective_counts ψ hψ F hF hd v hv,
    normalizedFourierSum_eq_projective_counts χ hχ F hF hd v hv]

/-- Compatibility with the project's literal integer-representative prime
complete sum; nonzero frequency is required after reduction modulo p. -/
theorem completeCubicSum_eq_projective_counts (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous d) (hd : 0 < d) (p : ℕ) [Fact p.Prime]
    (v : Fin n → ℤ) (hv : (fun i => (v i : ZMod p)) ≠ 0) :
    completeCubicSum F p v = (p : ℂ) *
      (1 + (p : ℂ) * (Nat.card (sectionPoints (map (Int.castRingHom (ZMod p)) F)
        (fun i => (v i : ZMod p))) : ℂ) -
        (Nat.card (zeroPoints (map (Int.castRingHom (ZMod p)) F)) : ℂ)) := by
  rw [PrimeSumAdapter.completeCubicSum_eq_prime_mul_zeroFiberSum F p v hv]
  have h := zeroFiberSum_eq_projective_counts (k := ZMod p) ZMod.stdAddChar
    (PrimeSumAdapter.stdAddChar_ne_one p) (map (Int.castRingHom (ZMod p)) F)
    (hF.map _) hd (fun i => (v i : ZMod p))
  simpa only [ZMod.card] using congrArg (fun z : ℂ => (p : ℂ)*z) h

end CubicTenVariables.ProjectiveFourierIdentity
