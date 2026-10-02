import CubicTenVariables.CRTCharacters
import HessianTheorem11.Geometry
import Mathlib.Logic.Equiv.Prod

/-!
# Exact CRT for actual modular matrix and Hessian kernels

The coordinate CRT transports the literal matrix equation to its two
reductions. For a polynomial Hessian the base point is reduced by those
same ring maps. No homogeneity or nondegeneracy assumption is needed.
-/

noncomputable section
namespace CubicTenVariables.HessianKernelCRT
open MvPolynomial HessianTheorem11 CRTCharacters
open scoped BigOperators

variable {d m n : ℕ}

/-- The actual nullspace cardinality of an integral matrix modulo `q`. -/
def kernelCard (B : Matrix (Fin d) (Fin d) ℤ) (q : ℕ) : ℕ :=
  Nat.card {z : Fin d → ZMod q // (B.map (Int.castRingHom (ZMod q))).mulVec z = 0}

/-- The actual Hessian of the reduced polynomial at a residue point. -/
def hessianKernelCard (F : MvPolynomial (Fin d) ℤ) (q : ℕ)
    (x : Fin d → ZMod q) : ℕ :=
  Nat.card {z : Fin d → ZMod q //
    (hessian (map (Int.castRingHom (ZMod q)) F) x).mulVec z = 0}

/-- Coordinatewise CRT preserves exactly the matrix nullspace equation. -/
theorem kernel_crt_iff (B : Matrix (Fin d) (Fin d) (ZMod (m*n)))
    (h : m.Coprime n) (z : Fin d → ZMod (m*n)) :
    B.mulVec z = 0 ↔
      (B.map (leftProjection h)).mulVec ((vectorEquiv h d z).1) = 0 ∧
      (B.map (rightProjection h)).mulVec ((vectorEquiv h d z).2) = 0 := by
  constructor
  · intro hz
    constructor
    · funext i
      have hi := congrArg (leftProjection h) (congrFun hz i)
      simpa only [RingHom.map_mulVec, Pi.zero_apply, map_zero,
        vectorEquiv_fst, Function.comp_def] using hi
    · funext i
      have hi := congrArg (rightProjection h) (congrFun hz i)
      simpa only [RingHom.map_mulVec, Pi.zero_apply, map_zero,
        vectorEquiv_snd, Function.comp_def] using hi
  · rintro ⟨hl, hr⟩
    funext i
    apply (ZMod.chineseRemainder h).injective
    apply Prod.ext
    · change leftProjection h (B.mulVec z i) = leftProjection h 0
      simpa only [RingHom.map_mulVec, Pi.zero_apply, map_zero,
        vectorEquiv_fst, Function.comp_def] using congrFun hl i
    · change rightProjection h (B.mulVec z i) = rightProjection h 0
      simpa only [RingHom.map_mulVec, Pi.zero_apply, map_zero,
        vectorEquiv_snd, Function.comp_def] using congrFun hr i

/-- CRT for any actual matrix over the product residue ring. -/
theorem natCard_kernel_crt (B : Matrix (Fin d) (Fin d) (ZMod (m*n)))
    (h : m.Coprime n) :
    Nat.card {z : Fin d → ZMod (m*n) // B.mulVec z = 0} =
      Nat.card {z : Fin d → ZMod m // (B.map (leftProjection h)).mulVec z = 0} *
      Nat.card {z : Fin d → ZMod n // (B.map (rightProjection h)).mulVec z = 0} := by
  let e₀ : {z : Fin d → ZMod (m*n) // B.mulVec z = 0} ≃
      {z : (Fin d → ZMod m) × (Fin d → ZMod n) //
        (B.map (leftProjection h)).mulVec z.1 = 0 ∧
        (B.map (rightProjection h)).mulVec z.2 = 0} :=
    Equiv.subtypeEquiv (vectorEquiv h d) (kernel_crt_iff B h)
  let e := e₀.trans (Equiv.subtypeProdEquivProd
    (p := fun z : Fin d → ZMod m => (B.map (leftProjection h)).mulVec z = 0)
    (q := fun z : Fin d → ZMod n => (B.map (rightProjection h)).mulVec z = 0))
  exact (Nat.card_congr e).trans (Nat.card_prod _ _)

/-- Exact kernel multiplicativity for an integral matrix. -/
theorem kernelCard_mul (B : Matrix (Fin d) (Fin d) ℤ) (h : m.Coprime n) :
    kernelCard B (m*n) = kernelCard B m * kernelCard B n := by
  have hl : leftProjection h ∘ Int.castRingHom (ZMod (m*n)) =
      (Int.castRingHom (ZMod m) : ℤ → ZMod m) := by funext k; exact map_intCast _ k
  have hr : rightProjection h ∘ Int.castRingHom (ZMod (m*n)) =
      (Int.castRingHom (ZMod n) : ℤ → ZMod n) := by funext k; exact map_intCast _ k
  simpa only [kernelCard, Matrix.map_map, hl, hr]
    using natCard_kernel_crt (B.map (Int.castRingHom (ZMod (m*n)))) h

/-- Evaluation of the actual second partials commutes with ring maps. -/
theorem hessian_map_eval {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : MvPolynomial (Fin d) R) (x : Fin d → R) :
    (hessian F x).map f = hessian (map f F) (fun i => f (x i)) := by
  ext i j
  simp only [hessian, hessianPolynomial, Matrix.map_apply, pderiv_map, eval_map]
  exact eval₂_comp f x _

/-- Reducing coefficients and the base point by any actual map between
residue rings gives exactly the reduced Hessian matrix. -/
theorem hessian_reduce (F : MvPolynomial (Fin d) ℤ)
    {a b : ℕ} (f : ZMod a →+* ZMod b) (x : Fin d → ZMod a) :
    (hessian (map (Int.castRingHom (ZMod a)) F) x).map f =
      hessian (map (Int.castRingHom (ZMod b)) F) (fun i => f (x i)) := by
  have hc : f.comp (Int.castRingHom (ZMod a)) = Int.castRingHom (ZMod b) :=
    Subsingleton.elim _ _
  rw [hessian_map_eval, map_map, hc]

/-- Exact CRT factorization with the actual projected Hessian centers. -/
theorem hessianKernelCard_mul (F : MvPolynomial (Fin d) ℤ) (h : m.Coprime n)
    (x : Fin d → ZMod (m*n)) :
    hessianKernelCard F (m*n) x =
      hessianKernelCard F m (fun i => leftProjection h (x i)) *
      hessianKernelCard F n (fun i => rightProjection h (x i)) := by
  simpa only [hessianKernelCard, hessian_reduce] using
    natCard_kernel_crt (hessian (map (Int.castRingHom (ZMod (m*n))) F) x) h

/-- An integral center gives the same kernel whether the Hessian is
evaluated before or after reducing coefficients and coordinates. -/
theorem hessianKernelCard_intCast (F : MvPolynomial (Fin d) ℤ) (q : ℕ)
    (x : Fin d → ℤ) :
    hessianKernelCard F q (fun i => (x i : ZMod q)) = kernelCard (hessian F x) q := by
  unfold hessianKernelCard kernelCard
  rw [hessian_map_eval]
  rfl

/-- The integer Hessian kernel depends only on the residue class of its
center, not on a chosen lift. -/
theorem kernelCard_hessian_congr (F : MvPolynomial (Fin d) ℤ) (q : ℕ)
    (x y : Fin d → ℤ) (hxy : ∀ i, (x i : ZMod q) = (y i : ZMod q)) :
    kernelCard (hessian F x) q = kernelCard (hessian F y) q := by
  rw [← hessianKernelCard_intCast, ← hessianKernelCard_intCast]
  congr 1
  funext i
  exact hxy i

/-- Canonical representatives are merely one possible lift of a residue center. -/
theorem hessianKernelCard_val (F : MvPolynomial (Fin d) ℤ) (q : ℕ) [NeZero q]
    (x : Fin d → ZMod q) :
    hessianKernelCard F q x = kernelCard (hessian F (fun i => (x i).val)) q := by
  rw [← hessianKernelCard_intCast]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

end CubicTenVariables.HessianKernelCRT
