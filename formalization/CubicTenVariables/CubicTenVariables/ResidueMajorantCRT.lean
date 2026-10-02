import CubicTenVariables.IntegerResidueClasses
import CubicTenVariables.PolynomialRootProductCRT

/-! Products of periodic majorants through the existing vector CRT maps.
Their masses are exact unnormalised residue sums. The finite-product form
also covers an empty family, whose modulus and majorant are both one. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ResidueMajorantCRT
open IntegerResidueClasses (residue)
open scoped BigOperators

variable {n a b : ℕ}

/-- The product majorant on the product modulus, using the literal CRT
projections rather than integer representative choices. -/
def product (hc : a.Coprime b)
    (P : (Fin n → ZMod a) → ℝ) (Q : (Fin n → ZMod b) → ℝ)
    (x : Fin n → ZMod (a*b)) : ℝ :=
  P (fun i => CRTCharacters.leftProjection hc (x i)) *
    Q (fun i => CRTCharacters.rightProjection hc (x i))

theorem product_nonneg (hc : a.Coprime b)
    (P : (Fin n → ZMod a) → ℝ) (Q : (Fin n → ZMod b) → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x) (x : Fin n → ZMod (a*b)) :
    0 ≤ product hc P Q x := mul_nonneg (hP _) (hQ _)

/-- The product is natural at every integer frequency. -/
theorem product_at_residue (hc : a.Coprime b)
    (P : (Fin n → ZMod a) → ℝ) (Q : (Fin n → ZMod b) → ℝ)
    (v : Fin n → ℤ) :
    product hc P Q (residue (a*b) v) = P (residue a v)*Q (residue b v) := by
  simp only [product,residue,map_intCast]
  rfl

/-- Exact mass factorisation. No nonnegativity assumption is needed for
this identity; the nonzero natural moduli are precisely positive moduli. -/
theorem product_mass [NeZero a] [NeZero b] (hc : a.Coprime b)
    (P : (Fin n → ZMod a) → ℝ) (Q : (Fin n → ZMod b) → ℝ) :
    (∑ x : Fin n → ZMod (a*b), product hc P Q x) =
      (∑ x : Fin n → ZMod a, P x)*(∑ y : Fin n → ZMod b, Q y) :=
  WeightedCRTAdapters.sum_crt_product hc P Q

/-- Two finite-set majorizations multiply without requiring anything
about the weights outside that finite set. -/
theorem product_majorizes (hc : a.Coprime b)
    (P : (Fin n → ZMod a) → ℝ) (Q : (Fin n → ZMod b) → ℝ)
    (V : Finset (Fin n → ℤ)) (w z : (Fin n → ℤ) → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) (hz : ∀ v ∈ V, 0 ≤ z v)
    (hP : ∀ v ∈ V, w v ≤ P (residue a v))
    (hQ : ∀ v ∈ V, z v ≤ Q (residue b v)) :
    ∀ v ∈ V, w v*z v ≤ product hc P Q (residue (a*b) v) := by
  intro v hv
  rw [product_at_residue]
  exact mul_le_mul (hP v hv) (hQ v hv) (hz v hv) ((hw v hv).trans (hP v hv))

/-- Upper bounds for the two masses multiply with no further loss. -/
theorem product_mass_le [NeZero a] [NeZero b] (hc : a.Coprime b)
    (P : (Fin n → ZMod a) → ℝ) (Q : (Fin n → ZMod b) → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x)
    (A B : ℝ) (hA : (∑ x, P x) ≤ A) (hB : (∑ y, Q y) ≤ B) :
    (∑ x : Fin n → ZMod (a*b), product hc P Q x) ≤ A*B := by
  rw [product_mass]
  exact mul_le_mul hA hB (Finset.sum_nonneg fun y _ => hQ y)
    ((Finset.sum_nonneg fun x _ => hP x).trans hA)

section FiniteProduct
variable {ι : Type*} [Fintype ι]

/-- A finite product of residue majorants on pairwise distinct prime-power
moduli, or more generally on any finite family of coprime positive moduli.
The construction itself uses the canonical reduction maps and needs no
coprimality assumption. -/
def piProduct (q : ι → ℕ) (P : ∀ i, (Fin n → ZMod (q i)) → ℝ)
    (x : Fin n → ZMod (∏ i, q i)) : ℝ :=
  ∏ i, P i (fun k => PolynomialRootProductCRT.projection q i (x k))

theorem piProduct_nonneg (q : ι → ℕ) (P : ∀ i, (Fin n → ZMod (q i)) → ℝ)
    (hP : ∀ i x, 0 ≤ P i x) (x : Fin n → ZMod (∏ i, q i)) :
    0 ≤ piProduct q P x := Finset.prod_nonneg fun i _ => hP i _

theorem piProduct_at_residue (q : ι → ℕ) (P : ∀ i, (Fin n → ZMod (q i)) → ℝ)
    (v : Fin n → ℤ) :
    piProduct q P (residue (∏ i, q i) v) = ∏ i, P i (residue (q i) v) := by
  simp only [piProduct,residue,map_intCast]
  rfl

/-- Exact finite CRT mass factorisation, including the empty family. -/
theorem piProduct_mass (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hc : Pairwise fun i j => (q i).Coprime (q j))
    (P : ∀ i, (Fin n → ZMod (q i)) → ℝ) :
    (∑ x : Fin n → ZMod (∏ i, q i), piProduct q P x) =
      ∏ i, ∑ y : Fin n → ZMod (q i), P i y :=
  PolynomialRootProductCRT.sum_product q hc n P

/-- Finite products of nonnegative local weights are bounded by the
finite CRT majorant at every supplied integer frequency. -/
theorem piProduct_majorizes (q : ι → ℕ) (P : ∀ i, (Fin n → ZMod (q i)) → ℝ)
    (V : Finset (Fin n → ℤ)) (w : ι → (Fin n → ℤ) → ℝ)
    (hw : ∀ i v, v ∈ V → 0 ≤ w i v)
    (hP : ∀ i v, v ∈ V → w i v ≤ P i (residue (q i) v)) :
    ∀ v ∈ V, (∏ i, w i v) ≤ piProduct q P (residue (∏ i, q i) v) := by
  intro v hv
  rw [piProduct_at_residue]
  exact Finset.prod_le_prod (fun i _ => hw i v hv) (fun i _ => hP i v hv)

/-- Any supplied nonnegative local mass bounds multiply without an
additional combinatorial factor. -/
theorem piProduct_mass_le (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hc : Pairwise fun i j => (q i).Coprime (q j))
    (P : ∀ i, (Fin n → ZMod (q i)) → ℝ) (hP : ∀ i x, 0 ≤ P i x)
    (A : ι → ℝ) (hA : ∀ i, (∑ x, P i x) ≤ A i) :
    (∑ x : Fin n → ZMod (∏ i, q i), piProduct q P x) ≤ ∏ i, A i := by
  rw [piProduct_mass q hc P]
  exact Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun x _ => hP i x) (fun i _ => hA i)

end FiniteProduct
end CubicTenVariables.ResidueMajorantCRT
