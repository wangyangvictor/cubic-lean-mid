import CubicTenVariables.QuadraticGaussBound

/-! The actual additive shift t modulo M -> d*t modulo d*M identifies
an integral matrix kernel modulo M with its kernel modulo d*M restricted
to shifts that reduce to zero modulo d. No primality is required. -/

noncomputable section
namespace CubicTenVariables.ResidueShiftKernel
open scoped BigOperators

variable (d M : ℕ)

/-- Additive multiplication into the larger residue ring, not a ring map. -/
def shiftHom : ZMod M →+ ZMod (d*M) :=
  ZMod.lift M ⟨{
    toFun := fun a : ℤ => (d : ZMod (d*M)) * (a : ZMod (d*M))
    map_zero' := by simp
    map_add' := by intro a b; simp [mul_add]
  }, by
    change (d : ZMod (d*M)) * ((M : ℤ) : ZMod (d*M)) = 0
    rw [Int.cast_natCast, ← Nat.cast_mul, ZMod.natCast_self]⟩

@[simp] theorem shiftHom_intCast (a : ℤ) :
    shiftHom d M (a : ZMod M) = ((d : ℤ)*a : ℤ) := by
  change ZMod.lift M _ (a : ZMod M) = _
  rw [ZMod.lift_coe]
  simp

@[simp] theorem shiftHom_zero_iff [NeZero d] (x : ZMod M) :
    shiftHom d M x = 0 ↔ x = 0 := by
  obtain ⟨a,rfl⟩ := ZMod.intCast_surjective x
  rw [shiftHom_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_mul]
  exact mul_dvd_mul_iff_left (by exact_mod_cast (NeZero.ne d))

theorem shiftHom_injective [NeZero d] : Function.Injective (shiftHom d M) := by
  intro x y hxy
  have h : shiftHom d M (x-y) = 0 := by rw [map_sub,hxy,sub_self]
  exact sub_eq_zero.mp ((shiftHom_zero_iff d M _).mp h)

/-- The actual reduction to the lower modulus. -/
def reduction : ZMod (d*M) →+* ZMod d :=
  ZMod.castHom (dvd_mul_right d M) (ZMod d)

@[simp] theorem reduction_shiftHom (x : ZMod M) :
    reduction d M (shiftHom d M x) = 0 := by
  obtain ⟨a,rfl⟩ := ZMod.intCast_surjective x
  rw [shiftHom_intCast, map_intCast]
  simp

theorem exists_shift_of_reduction_zero (x : ZMod (d*M))
    (hx : reduction d M x = 0) : ∃ t : ZMod M, shiftHom d M t = x := by
  obtain ⟨a,rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
  obtain ⟨t,rfl⟩ := hx
  exact ⟨(t : ZMod M), shiftHom_intCast d M t⟩

/-- Integral matrix multiplication commutes with the additive shift. -/
theorem mulVec_shift {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (t : Fin n → ZMod M) :
    (B.map (Int.castRingHom (ZMod (d*M)))).mulVec (fun i => shiftHom d M (t i)) =
      fun i => shiftHom d M ((B.map (Int.castRingHom (ZMod M))).mulVec t i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [zsmul_eq_mul] using (map_zsmul (shiftHom d M) (B i j) (t j)).symm

/-- Exact count of the matrix kernel restricted to shifts zero modulo d. -/
theorem card_restricted_kernel {n : ℕ} [NeZero d] [NeZero M]
    (B : Matrix (Fin n) (Fin n) ℤ) :
    Nat.card {z : Fin n → ZMod (d*M) //
      (∀ i, reduction d M (z i) = 0) ∧
      (B.map (Int.castRingHom (ZMod (d*M)))).mulVec z = 0} =
    Nat.card {t : Fin n → ZMod M //
      (B.map (Int.castRingHom (ZMod M))).mulVec t = 0} := by
  classical
  let f : {t : Fin n → ZMod M // (B.map (Int.castRingHom (ZMod M))).mulVec t = 0} →
      {z : Fin n → ZMod (d*M) // (∀ i, reduction d M (z i) = 0) ∧
        (B.map (Int.castRingHom (ZMod (d*M)))).mulVec z = 0} := fun t =>
    ⟨fun i => shiftHom d M (t.1 i), fun i => reduction_shiftHom d M _, by
      rw [mulVec_shift, t.2]
      simp
      rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      funext i
      exact shiftHom_injective d M (congrFun (congrArg Subtype.val hxy) i)
    · intro z
      choose t ht using fun i => exists_shift_of_reduction_zero d M (z.1 i) (z.2.1 i)
      have he : (fun i => shiftHom d M (t i)) = z.1 := funext ht
      have hk : (B.map (Int.castRingHom (ZMod M))).mulVec t = 0 := by
        funext i
        apply (shiftHom_zero_iff d M _).mp
        have hz := congrFun z.2.2 i
        rw [← he, mulVec_shift] at hz
        exact hz
      exact ⟨⟨t,hk⟩, Subtype.ext he⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

/-- The same exact kernel identity at a positive modulus and any divisor. -/
theorem card_restricted_kernel_div {n : ℕ} (c d : ℕ) [NeZero c] [NeZero d]
    (hdc : d ∣ c) (B : Matrix (Fin n) (Fin n) ℤ) :
    Nat.card {z : Fin n → ZMod c //
      (∀ i, ZMod.castHom hdc (ZMod d) (z i) = 0) ∧
      (B.map (Int.castRingHom (ZMod c))).mulVec z = 0} =
    Nat.card {t : Fin n → ZMod (c/d) //
      (B.map (Int.castRingHom (ZMod (c/d)))).mulVec t = 0} := by
  obtain ⟨M,rfl⟩ := hdc
  have hM : M ≠ 0 := by
    intro h
    exact (NeZero.ne (d*M)) (by simp [h])
  letI : NeZero M := ⟨hM⟩
  rw [Nat.mul_div_cancel_left M (Nat.pos_of_ne_zero (NeZero.ne d))]
  exact card_restricted_kernel d M B

end CubicTenVariables.ResidueShiftKernel
