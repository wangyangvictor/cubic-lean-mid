import CubicTenVariables.AdmissibleResidueFibers
import Mathlib.GroupTheory.Index

/-! Exact counting ratio for admissible canonical low digits.
The quotient-image construction uses genuine representatives and their
carries, with no homomorphism from the smaller residue ring to the larger.
-/

noncomputable section
namespace CubicTenVariables.AdmissibleResidueCount
open AdmissibleResidueFibers
open scoped BigOperators Matrix

/-- Elementary finite first-isomorphism cardinality identity. -/
theorem card_kernel_mul_range {G H : Type*} [AddGroup G] [AddGroup H]
    (f : G →+ H) : Nat.card f.ker * Nat.card f.range = Nat.card G := by
  rw [← AddSubgroup.index_ker]
  exact f.ker.card_mul_index

/-- The inverse image of a subgroup contained in the range has the expected size. -/
theorem card_preimage_of_subset_range {G H : Type*} [AddGroup G] [AddGroup H]
    [Finite G] [Finite H] (f : G →+ H) (K : AddSubgroup H)
    (hK : ∀ k : K, ∃ x : G, f x = (k : H)) :
    Nat.card {x : G // f x ∈ K} = Nat.card K * Nat.card f.ker := by
  classical
  letI := Fintype.ofFinite K
  let e : {x : G // f x ∈ K} ≃ (Σ k : K, {x : G // f x = (k : H)}) :=
    { toFun := fun x => ⟨⟨f x, x.property⟩, ⟨x, rfl⟩⟩
      invFun := fun kx => ⟨kx.2, by rw [kx.2.property]; exact kx.1.property⟩
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨k,hk⟩,⟨x,hx⟩⟩; cases hx; rfl }
  have hc (k : K) : Nat.card {x : G // f x = (k : H)} = Nat.card f.ker := by
    obtain ⟨x,hx⟩ := hK k
    change Nat.card (f ⁻¹' {(k : H)}) = _
    rw [← hx]
    exact Nat.card_congr (f.fiberEquivKer x)
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, Nat.cast_id]

variable (M L n : ℕ) [NeZero M] [NeZero L]

/-- Every target residue vector decomposes as a canonical low digit plus
an actual multiple of L, for arbitrary positive M,L. -/
theorem exists_canonicalLift_decomposition (w : Fin n → ZMod M) :
    ∃ (v : Fin n → ZMod L) (c : Fin n → ZMod M),
      w = canonicalLift M L n v + (L : ZMod M) • c := by
  refine ⟨fun i => ((w i).val : ZMod L), fun i => ((w i).val / L : ℕ), ?_⟩
  ext i
  have hi := congrArg (fun z : ℕ => (z : ZMod M)) (Nat.mod_add_div (w i).val L)
  simpa only [canonicalLift, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    ZMod.val_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val] using hi.symm

/-- The low-digit quotient map and the full target-residue quotient map
have exactly the same image. -/
theorem quotientMap_range (H : Matrix (Fin n) (Fin n) (ZMod M)) :
    (quotientMap M L n H).range =
      (((scaledImage M L n H).mkQ.comp H.mulVecLin).toAddMonoidHom).range := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨canonicalLift M L n v, rfl⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v,c,hc⟩ := exists_canonicalLift_decomposition M L n w
    refine ⟨v, ?_⟩
    change (scaledImage M L n H).mkQ (H.mulVec (canonicalLift M L n v)) =
      (scaledImage M L n H).mkQ (H.mulVec w)
    rw [hc, Matrix.mulVec_add, map_add]
    have hz : (scaledImage M L n H).mkQ (H.mulVec ((L : ZMod M) • c)) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero (scaledImage M L n H)).mpr
      refine ⟨c, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.mulVec_smul]
    rw [hz, add_zero]

/-- Exact homogeneous low-digit count times the scaled kernel equals
L^n times the original kernel. No diagonal data are supplied as input. -/
theorem card_homogeneous_mul_card_scaled_kernel
    (H : Matrix (Fin n) (Fin n) (ZMod M)) :
    Nat.card {v : Fin n → ZMod L //
      ∃ x : Fin n → ZMod M,
        ((L : ZMod M) • H).mulVec x = H.mulVec (canonicalLift M L n v)} *
      Nat.card {x : Fin n → ZMod M // ((L : ZMod M) • H).mulVec x = 0} =
    L^n * Nat.card {x : Fin n → ZMod M // H.mulVec x = 0} := by
  classical
  let N := scaledImage M L n H
  let f := H.mulVecLin.toAddMonoidHom
  let g := (((L : ZMod M) • H).mulVecLin).toAddMonoidHom
  let h := (N.mkQ.comp H.mulVecLin).toAddMonoidHom
  let l := quotientMap M L n H
  have hN : ∀ k : N.toAddSubgroup, ∃ x : Fin n → ZMod M, f x = (k : Fin n → ZMod M) := by
    rintro ⟨k, x, hx⟩
    refine ⟨(L : ZMod M) • x, ?_⟩
    change H.mulVec ((L : ZMod M) • x) = k
    simpa only [Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.mulVec_smul] using hx
  have hk : Nat.card h.ker = Nat.card N * Nat.card f.ker := by
    have he : h.ker ≃ {x : Fin n → ZMod M // f x ∈ N.toAddSubgroup} :=
      Equiv.subtypeEquivRight (fun x => Submodule.Quotient.mk_eq_zero N)
    exact (Nat.card_congr he).trans (card_preimage_of_subset_range f N.toAddSubgroup hN)
  have hfull := card_kernel_mul_range h
  have hg := card_kernel_mul_range g
  have hlow := card_kernel_mul_range l
  have hrange : l.range = h.range := quotientMap_range M L n H
  have hgrange : Nat.card g.range = Nat.card N := rfl
  have hG : Nat.card (Fin n → ZMod M) = M^n := by simp [Nat.card_fun, Nat.card_zmod]
  have hV : Nat.card (Fin n → ZMod L) = L^n := by simp [Nat.card_fun, Nat.card_zmod]
  rw [hk, hG] at hfull
  rw [hgrange, hG] at hg
  rw [hrange, hV] at hlow
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hratio : Nat.card f.ker * Nat.card h.range = Nat.card g.ker := by
    apply Nat.eq_of_mul_eq_mul_left hNpos
    calc
      Nat.card N * (Nat.card f.ker * Nat.card h.range) = M^n := by
        simpa only [mul_assoc] using hfull
      _ = Nat.card N * Nat.card g.ker := by simpa only [mul_comm] using hg.symm
  have hmain : Nat.card l.ker * Nat.card g.ker = L^n * Nat.card f.ker := by
    rw [← hratio]
    calc
      Nat.card l.ker * (Nat.card f.ker * Nat.card h.range) =
          (Nat.card l.ker * Nat.card h.range) * Nat.card f.ker := by ring
      _ = _ := by rw [hlow]
  have hlker : l.ker ≃ {v : Fin n → ZMod L // ∃ x : Fin n → ZMod M,
      ((L : ZMod M) • H).mulVec x = H.mulVec (canonicalLift M L n v)} :=
    Equiv.subtypeEquivRight (fun v => Submodule.Quotient.mk_eq_zero N)
  rw [Nat.card_congr hlker] at hmain
  exact hmain

/-- Exact count ratio for every nonempty affine admissible fiber. -/
theorem card_admissible_mul_card_scaled_kernel_of_nonempty
    (H : Matrix (Fin n) (Fin n) (ZMod M))
    (ell : Fin n → ZMod M) (alpha : (ZMod M)ˣ)
    (hv : ∃ v, admissible M L n H ell alpha v) :
    Nat.card {v : Fin n → ZMod L // admissible M L n H ell alpha v} *
      Nat.card {x : Fin n → ZMod M // ((L : ZMod M) • H).mulVec x = 0} =
    L^n * Nat.card {x : Fin n → ZMod M // H.mulVec x = 0} := by
  rw [card_admissible_eq_homogeneous_of_nonempty M L n H ell alpha hv]
  exact card_homogeneous_mul_card_scaled_kernel M L n H

/-- Actual Fin representatives and actual residue classes give the same
admissible count. Only the representatives' value is cast between moduli. -/
theorem card_admissible_fin_eq
    (H : Matrix (Fin n) (Fin n) (ZMod M))
    (ell : Fin n → ZMod M) (alpha : (ZMod M)ˣ) :
    Nat.card {v : Fin n → Fin L // ∃ x : Fin n → ZMod M,
      ((L : ZMod M) • H).mulVec x =
        ell + (alpha : ZMod M) • H.mulVec (fun i => ((v i).val : ZMod M))} =
    Nat.card {v : Fin n → ZMod L // admissible M L n H ell alpha v} := by
  apply Nat.card_congr
  apply (PrimeSumAdapter.vectorResidueEquiv L n).subtypeEquiv
  intro v
  have hv : canonicalLift M L n (PrimeSumAdapter.vectorResidueEquiv L n v) =
      fun i => ((v i).val : ZMod M) := by
    ext i
    simp only [canonicalLift, PrimeSumAdapter.vectorResidueEquiv_apply, ZMod.val_natCast,
      Nat.mod_eq_of_lt (v i).isLt]
  simp only [admissible, hv]

/-- The exact zero-or-ratio statement on the manuscript's actual finite
low-digit representatives. This includes both relative orders of M and L. -/
theorem card_admissible_fin_eq_zero_or_ratio
    (H : Matrix (Fin n) (Fin n) (ZMod M))
    (ell : Fin n → ZMod M) (alpha : (ZMod M)ˣ) :
    Nat.card {v : Fin n → Fin L // ∃ x : Fin n → ZMod M,
      ((L : ZMod M) • H).mulVec x =
        ell + (alpha : ZMod M) • H.mulVec (fun i => ((v i).val : ZMod M))} = 0 ∨
    Nat.card {v : Fin n → Fin L // ∃ x : Fin n → ZMod M,
      ((L : ZMod M) • H).mulVec x =
        ell + (alpha : ZMod M) • H.mulVec (fun i => ((v i).val : ZMod M))} *
      Nat.card {x : Fin n → ZMod M // ((L : ZMod M) • H).mulVec x = 0} =
    L^n * Nat.card {x : Fin n → ZMod M // H.mulVec x = 0} := by
  rw [card_admissible_fin_eq M L n H ell alpha]
  rcases card_admissible_eq_zero_or_homogeneous M L n H ell alpha with hz | he
  · exact Or.inl hz
  · right
    rw [he]
    exact card_homogeneous_mul_card_scaled_kernel M L n H

end CubicTenVariables.AdmissibleResidueCount
