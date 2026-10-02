import Mathlib.Algebra.MvPolynomial.Eval
import TranslatedDepthSeven.SquarefreeProjectionResidueCount

/-!
# Polynomial zero sets and exact square-free Chinese remaindering

This file identifies a literal common zero set of integral multivariate
polynomials modulo a square-free product with the product of its reductions
modulo the prime factors.  The proof is purely algebraic: polynomial
evaluation commutes with every component ring homomorphism of the Chinese
remainder equivalence.

The final statements combine this exact identification with the elementary
coordinate-fibre count from `SquarefreeProjectionResidueCount`.
-/

namespace TranslatedDepthSeven

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluation of an integral multivariate polynomial after reducing its
coefficients in `ZMod q`. -/
def integerPolynomialValue {N q : ℕ}
    (f : MvPolynomial (Fin N) ℤ) (x : Fin N → ZMod q) : ZMod q :=
  f.eval₂ (Int.castRingHom (ZMod q)) x

/-- The literal common zero set modulo `q` of the finite family `polynomials`.
-/
def integerPolynomialZeroSet (q N : ℕ) (hzero : q ≠ 0)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ)) :
    Finset (Fin N → ZMod q) := by
  letI : NeZero q := ⟨hzero⟩
  exact Finset.univ.filter fun x ↦
    ∀ f ∈ polynomials, integerPolynomialValue f x = 0

@[simp]
theorem mem_integerPolynomialZeroSet_iff
    {q N : ℕ} {hzero : q ≠ 0}
    {polynomials : Finset (MvPolynomial (Fin N) ℤ)}
    {x : Fin N → ZMod q} :
    x ∈ integerPolynomialZeroSet q N hzero polynomials ↔
      ∀ f ∈ polynomials, integerPolynomialValue f x = 0 := by
  letI : NeZero q := ⟨hzero⟩
  simp [integerPolynomialZeroSet]

/-- Changing a positive modulus along an equality does not change the
cardinality of the corresponding integral-polynomial zero set.  Stating this
elementary transport explicitly avoids exposing dependent casts between
propositionally equal `ZMod` types in downstream theorems. -/
theorem card_integerPolynomialZeroSet_congr_modulus
    {q r N : ℕ} (hqr : q = r) (hq : q ≠ 0) (hr : r ≠ 0)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ)) :
    (integerPolynomialZeroSet q N hq polynomials).card =
      (integerPolynomialZeroSet r N hr polynomials).card := by
  subst r
  rfl

/-- The `i`th component ring homomorphism of the finite CRT equivalence. -/
def crtComponentRingHom (a : ι → ℕ)
    (hcop : Pairwise (Function.onFun Nat.Coprime a)) (i : ι) :
    ZMod (∏ j, a j) →+* ZMod (a i) :=
  (Pi.evalRingHom (fun j ↦ ZMod (a j)) i).comp
    (ZMod.prodEquivPi a hcop).toRingHom

omit [DecidableEq ι] in
@[simp]
theorem crtComponentRingHom_apply (a : ι → ℕ)
    (hcop : Pairwise (Function.onFun Nat.Coprime a)) (i : ι)
    (z : ZMod (∏ j, a j)) :
    crtComponentRingHom a hcop i z = ZMod.prodEquivPi a hcop z i :=
  rfl

omit [DecidableEq ι] in
/-- Integral polynomial evaluation commutes exactly with every component of
the coordinatewise Chinese-remainder map. -/
theorem integerPolynomialValue_crt_component
    (a : ι → ℕ) (hcop : Pairwise (Function.onFun Nat.Coprime a))
    {N : ℕ} (f : MvPolynomial (Fin N) ℤ)
    (x : Fin N → ZMod (∏ i, a i)) (i : ι) :
    ZMod.prodEquivPi a hcop (integerPolynomialValue f x) i =
      integerPolynomialValue f (crtVectorEquiv a hcop N x i) := by
  let k : ZMod (∏ i, a i) →+* ZMod (a i) :=
    crtComponentRingHom a hcop i
  calc
    ZMod.prodEquivPi a hcop (integerPolynomialValue f x) i =
        k (integerPolynomialValue f x) := rfl
    _ = f.eval₂ (k.comp (Int.castRingHom (ZMod (∏ i, a i)))) (k ∘ x) :=
      MvPolynomial.eval₂_comp_left k (Int.castRingHom _) x f
    _ = f.eval₂ (Int.castRingHom (ZMod (a i)))
        (crtVectorEquiv a hcop N x i) := by
      congr 1
      · exact RingHom.ext_int _ _

omit [DecidableEq ι] in
/-- A global integral polynomial value vanishes modulo the square-free
product if and only if all of its CRT components vanish. -/
theorem integerPolynomialValue_eq_zero_iff_crt
    (a : ι → ℕ) (hcop : Pairwise (Function.onFun Nat.Coprime a))
    {N : ℕ} (f : MvPolynomial (Fin N) ℤ)
    (x : Fin N → ZMod (∏ i, a i)) :
    integerPolynomialValue f x = 0 ↔
      ∀ i, integerPolynomialValue f (crtVectorEquiv a hcop N x i) = 0 := by
  constructor
  · intro hx i
    rw [← integerPolynomialValue_crt_component a hcop f x i, hx]
    exact map_zero (crtComponentRingHom a hcop i)
  · intro hx
    apply (ZMod.prodEquivPi a hcop).injective
    funext i
    rw [integerPolynomialValue_crt_component a hcop f x i, hx i]
    exact (map_zero (crtComponentRingHom a hcop i)).symm

omit [DecidableEq ι] in
/-- Exact membership compatibility for a finite family of integral
polynomials. -/
theorem mem_integerPolynomialZeroSet_product_iff
    (a : ι → ℕ) (hcop : Pairwise (Function.onFun Nat.Coprime a))
    (hzero : ∀ i, a i ≠ 0) (N : ℕ)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (x : Fin N → ZMod (∏ i, a i)) :
    x ∈ integerPolynomialZeroSet (∏ i, a i) N
        (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hzero i) polynomials ↔
      ∀ i, crtVectorEquiv a hcop N x i ∈
        integerPolynomialZeroSet (a i) N (hzero i) polynomials := by
  letI (i : ι) : NeZero (a i) := ⟨hzero i⟩
  letI : NeZero (∏ i, a i) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun i _ ↦ hzero i⟩
  rw [mem_integerPolynomialZeroSet_iff]
  constructor
  · intro hx i
    rw [mem_integerPolynomialZeroSet_iff]
    intro f hf
    exact (integerPolynomialValue_eq_zero_iff_crt a hcop f x).mp (hx f hf) i
  · intro hx f hf
    apply (integerPolynomialValue_eq_zero_iff_crt a hcop f x).mpr
    intro i
    exact (mem_integerPolynomialZeroSet_iff.mp (hx i)) f hf

omit [DecidableEq ι] in
/-- The common zero set modulo the product is literally the CRT global
residue set attached to the common zero sets modulo the factors. -/
theorem integerPolynomialZeroSet_product_eq_crtGlobalResidues
    (a : ι → ℕ) (hcop : Pairwise (Function.onFun Nat.Coprime a))
    (hzero : ∀ i, a i ≠ 0) (N : ℕ)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ)) :
    integerPolynomialZeroSet (∏ i, a i) N
        (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hzero i) polynomials =
      crtGlobalResidues a hcop hzero N
        (fun i ↦ integerPolynomialZeroSet (a i) N (hzero i) polynomials) := by
  letI (i : ι) : NeZero (a i) := ⟨hzero i⟩
  letI : NeZero (∏ i, a i) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun i _ ↦ hzero i⟩
  ext x
  rw [mem_integerPolynomialZeroSet_product_iff a hcop hzero]
  exact mem_crtGlobalResidues_iff.symm

/-- Exact multiplication of the cardinalities of the common zero sets of a
finite family of integral polynomials modulo pairwise coprime factors. -/
theorem card_integerPolynomialZeroSet_product
    (a : ι → ℕ) (hcop : Pairwise (Function.onFun Nat.Coprime a))
    (hzero : ∀ i, a i ≠ 0) (N : ℕ)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ)) :
    (integerPolynomialZeroSet (∏ i, a i) N
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hzero i) polynomials).card =
      ∏ i, (integerPolynomialZeroSet (a i) N (hzero i) polynomials).card := by
  letI (i : ι) : NeZero (a i) := ⟨hzero i⟩
  letI : NeZero (∏ i, a i) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun i _ ↦ hzero i⟩
  rw [integerPolynomialZeroSet_product_eq_crtGlobalResidues a hcop hzero]
  exact card_crtGlobalResidues a hcop hzero N _

/-- Exact CRT cardinality multiplication stated on the manuscript's literal
reservoir modulus `primeProduct P`, rather than on the propositionally equal
product indexed by the subtype `P`. -/
theorem card_integerPolynomialZeroSet_primeProduct
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (N : ℕ)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ)) :
    (integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card =
      ∏ p : P,
        (integerPolynomialZeroSet (p : ℕ) N
          (primeSubtype_ne_zero hprime p) polynomials).card := by
  let hsubzero : (∏ p : P, (p : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ ↦ primeSubtype_ne_zero hprime p
  calc
    (integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card =
        (integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
          hsubzero polynomials).card :=
      card_integerPolynomialZeroSet_congr_modulus
        (primeSubtype_prod_eq_primeProduct P).symm _ _ polynomials
    _ = ∏ p : P,
        (integerPolynomialZeroSet (p : ℕ) N
          (primeSubtype_ne_zero hprime p) polynomials).card :=
      card_integerPolynomialZeroSet_product
        (fun p : P ↦ (p : ℕ))
        (primeSubtype_pairwise_coprime hprime)
        (primeSubtype_ne_zero hprime) N polynomials

/-- Local fibre bounds for arbitrary explicit maps on the actual polynomial
common zero sets imply the square-free product bound.  In particular, the
maps may be prime-dependent linear or affine-linear normalisations. -/
theorem card_integerPolynomialZeroSet_squarefreeProduct_le_of_map_fibers
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d D : ℕ)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (projection : ∀ p : P,
      (Fin N → ZMod (p : ℕ)) → (Fin d → ZMod (p : ℕ)))
    (hfibre : ∀ (p : P) (y : Fin d → ZMod (p : ℕ)),
      (finiteMapFiber (projection p)
        (integerPolynomialZeroSet (p : ℕ) N
          (primeSubtype_ne_zero hprime p) polynomials) y).card ≤ D) :
    (integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
      (Finset.prod_ne_zero_iff.mpr fun p _ ↦
        primeSubtype_ne_zero hprime p) polynomials).card ≤
      D ^ P.card * (primeProduct P) ^ d := by
  let hcop := primeSubtype_pairwise_coprime hprime
  let hzero := primeSubtype_ne_zero hprime
  letI (p : P) : NeZero (p : ℕ) := ⟨hzero p⟩
  letI : NeZero (∏ p : P, (p : ℕ)) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun p _ ↦ hzero p⟩
  rw [integerPolynomialZeroSet_product_eq_crtGlobalResidues
    (fun p : P ↦ (p : ℕ)) hcop hzero]
  exact card_squarefreePrime_crtGlobalResidues_le_of_map_fibers
    P hprime N d D projection
      (fun p ↦ integerPolynomialZeroSet (p : ℕ) N (hzero p) polynomials) hfibre

/-- The arbitrary-map fibre estimate stated directly modulo the reservoir
integer `primeProduct P`. -/
theorem card_integerPolynomialZeroSet_primeProduct_le_of_map_fibers
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d D : ℕ)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (projection : ∀ p : P,
      (Fin N → ZMod (p : ℕ)) → (Fin d → ZMod (p : ℕ)))
    (hfibre : ∀ (p : P) (y : Fin d → ZMod (p : ℕ)),
      (finiteMapFiber (projection p)
        (integerPolynomialZeroSet (p : ℕ) N
          (primeSubtype_ne_zero hprime p) polynomials) y).card ≤ D) :
    (integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card ≤
      D ^ P.card * (primeProduct P) ^ d := by
  let hsubzero : (∏ p : P, (p : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ ↦ primeSubtype_ne_zero hprime p
  calc
    (integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card =
        (integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
          hsubzero polynomials).card :=
      card_integerPolynomialZeroSet_congr_modulus
        (primeSubtype_prod_eq_primeProduct P).symm _ _ polynomials
    _ ≤ D ^ P.card * (primeProduct P) ^ d :=
      card_integerPolynomialZeroSet_squarefreeProduct_le_of_map_fibers
        P hprime N d D polynomials projection hfibre

/-- The arbitrary-map actual-zero-set estimate with the fixed fibre constant
absorbed into H^epsilon by the reservoir-depth bound. -/
theorem card_integerPolynomialZeroSet_squarefreeProduct_cast_le_rpow_mul_of_map_fibers
    {M0 ε H : ℝ} (hM0 : 0 ≤ M0) (hε : 0 < ε)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d D : ℕ) (hD : 1 ≤ D)
    (hPcard : P.card ≤ reservoirDepth M0 H)
    (hH : reservoirSubpowerThreshold M0 (D : ℝ) ε ≤ H)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (projection : ∀ p : P,
      (Fin N → ZMod (p : ℕ)) → (Fin d → ZMod (p : ℕ)))
    (hfibre : ∀ (p : P) (y : Fin d → ZMod (p : ℕ)),
      (finiteMapFiber (projection p)
        (integerPolynomialZeroSet (p : ℕ) N
          (primeSubtype_ne_zero hprime p) polynomials) y).card ≤ D) :
    ((integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
      (Finset.prod_ne_zero_iff.mpr fun p _ ↦
        primeSubtype_ne_zero hprime p) polynomials).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ d := by
  let hcop := primeSubtype_pairwise_coprime hprime
  let hzero := primeSubtype_ne_zero hprime
  letI (p : P) : NeZero (p : ℕ) := ⟨hzero p⟩
  letI : NeZero (∏ p : P, (p : ℕ)) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun p _ ↦ hzero p⟩
  rw [integerPolynomialZeroSet_product_eq_crtGlobalResidues
    (fun p : P ↦ (p : ℕ)) hcop hzero]
  exact card_squarefreePrime_crtGlobalResidues_cast_le_rpow_mul_of_map_fibers
    hM0 hε P hprime N d D hD hPcard hH projection
      (fun p ↦ integerPolynomialZeroSet (p : ℕ) N (hzero p) polynomials) hfibre

/-- The subpower arbitrary-map estimate stated directly modulo
`primeProduct P`. -/
theorem card_integerPolynomialZeroSet_primeProduct_cast_le_rpow_mul_of_map_fibers
    {M0 ε H : ℝ} (hM0 : 0 ≤ M0) (hε : 0 < ε)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d D : ℕ) (hD : 1 ≤ D)
    (hPcard : P.card ≤ reservoirDepth M0 H)
    (hH : reservoirSubpowerThreshold M0 (D : ℝ) ε ≤ H)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (projection : ∀ p : P,
      (Fin N → ZMod (p : ℕ)) → (Fin d → ZMod (p : ℕ)))
    (hfibre : ∀ (p : P) (y : Fin d → ZMod (p : ℕ)),
      (finiteMapFiber (projection p)
        (integerPolynomialZeroSet (p : ℕ) N
          (primeSubtype_ne_zero hprime p) polynomials) y).card ≤ D) :
    ((integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ d := by
  let hsubzero : (∏ p : P, (p : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ ↦ primeSubtype_ne_zero hprime p
  calc
    ((integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card : ℝ) =
        ((integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
          hsubzero polynomials).card : ℝ) := by
      exact_mod_cast card_integerPolynomialZeroSet_congr_modulus
        (primeSubtype_prod_eq_primeProduct P).symm
        (primeProduct_ne_zero fun p hp ↦ hprime p hp) hsubzero polynomials
    _ ≤ H ^ ε * (primeProduct P : ℝ) ^ d :=
      card_integerPolynomialZeroSet_squarefreeProduct_cast_le_rpow_mul_of_map_fibers
        hM0 hε P hprime N d D hD hPcard hH polynomials projection hfibre

/-- Local coordinate-fibre bounds for the actual polynomial common zero
sets imply the square-free product bound. -/
theorem card_integerPolynomialZeroSet_squarefreeProduct_le_of_projection_fibers
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d D : ℕ)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (coordinates : P → Fin d → Fin N)
    (hfibre : ∀ (p : P) (y : Fin d → ZMod (p : ℕ)),
      (finiteCoordinateProjectionFiber (coordinates p)
        (integerPolynomialZeroSet (p : ℕ) N
          (primeSubtype_ne_zero hprime p) polynomials) y).card ≤ D) :
    (integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
      (Finset.prod_ne_zero_iff.mpr fun p _ ↦
        primeSubtype_ne_zero hprime p) polynomials).card ≤
      D ^ P.card * (primeProduct P) ^ d := by
  let hcop := primeSubtype_pairwise_coprime hprime
  let hzero := primeSubtype_ne_zero hprime
  letI (p : P) : NeZero (p : ℕ) := ⟨hzero p⟩
  letI : NeZero (∏ p : P, (p : ℕ)) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun p _ ↦ hzero p⟩
  rw [integerPolynomialZeroSet_product_eq_crtGlobalResidues
    (fun p : P ↦ (p : ℕ)) hcop hzero]
  exact card_squarefreePrime_crtGlobalResidues_le_of_projection_fibers
    P hprime N d D coordinates
      (fun p ↦ integerPolynomialZeroSet (p : ℕ) N (hzero p) polynomials) hfibre

/-- The coordinate-projection fibre estimate stated directly modulo the
reservoir integer `primeProduct P`. -/
theorem card_integerPolynomialZeroSet_primeProduct_le_of_projection_fibers
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d D : ℕ)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (coordinates : P → Fin d → Fin N)
    (hfibre : ∀ (p : P) (y : Fin d → ZMod (p : ℕ)),
      (finiteCoordinateProjectionFiber (coordinates p)
        (integerPolynomialZeroSet (p : ℕ) N
          (primeSubtype_ne_zero hprime p) polynomials) y).card ≤ D) :
    (integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card ≤
      D ^ P.card * (primeProduct P) ^ d := by
  let hsubzero : (∏ p : P, (p : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ ↦ primeSubtype_ne_zero hprime p
  calc
    (integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card =
        (integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
          hsubzero polynomials).card :=
      card_integerPolynomialZeroSet_congr_modulus
        (primeSubtype_prod_eq_primeProduct P).symm _ _ polynomials
    _ ≤ D ^ P.card * (primeProduct P) ^ d :=
      card_integerPolynomialZeroSet_squarefreeProduct_le_of_projection_fibers
        P hprime N d D polynomials coordinates hfibre

/-- The same actual-zero-set estimate with the fixed fibre constant absorbed
into `H^ε` by the reservoir-depth bound. -/
theorem card_integerPolynomialZeroSet_squarefreeProduct_cast_le_rpow_mul_of_projection_fibers
    {M0 ε H : ℝ} (hM0 : 0 ≤ M0) (hε : 0 < ε)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d D : ℕ) (hD : 1 ≤ D)
    (hPcard : P.card ≤ reservoirDepth M0 H)
    (hH : reservoirSubpowerThreshold M0 (D : ℝ) ε ≤ H)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (coordinates : P → Fin d → Fin N)
    (hfibre : ∀ (p : P) (y : Fin d → ZMod (p : ℕ)),
      (finiteCoordinateProjectionFiber (coordinates p)
        (integerPolynomialZeroSet (p : ℕ) N
          (primeSubtype_ne_zero hprime p) polynomials) y).card ≤ D) :
    ((integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
      (Finset.prod_ne_zero_iff.mpr fun p _ ↦
        primeSubtype_ne_zero hprime p) polynomials).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ d := by
  let hcop := primeSubtype_pairwise_coprime hprime
  let hzero := primeSubtype_ne_zero hprime
  letI (p : P) : NeZero (p : ℕ) := ⟨hzero p⟩
  letI : NeZero (∏ p : P, (p : ℕ)) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun p _ ↦ hzero p⟩
  rw [integerPolynomialZeroSet_product_eq_crtGlobalResidues
    (fun p : P ↦ (p : ℕ)) hcop hzero]
  exact
    card_squarefreePrime_crtGlobalResidues_cast_le_rpow_mul_of_projection_fibers
      hM0 hε P hprime N d D hD hPcard hH coordinates
        (fun p ↦ integerPolynomialZeroSet (p : ℕ) N (hzero p) polynomials) hfibre

/-- The subpower coordinate-projection estimate stated directly modulo
`primeProduct P`. -/
theorem card_integerPolynomialZeroSet_primeProduct_cast_le_rpow_mul_of_projection_fibers
    {M0 ε H : ℝ} (hM0 : 0 ≤ M0) (hε : 0 < ε)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d D : ℕ) (hD : 1 ≤ D)
    (hPcard : P.card ≤ reservoirDepth M0 H)
    (hH : reservoirSubpowerThreshold M0 (D : ℝ) ε ≤ H)
    (polynomials : Finset (MvPolynomial (Fin N) ℤ))
    (coordinates : P → Fin d → Fin N)
    (hfibre : ∀ (p : P) (y : Fin d → ZMod (p : ℕ)),
      (finiteCoordinateProjectionFiber (coordinates p)
        (integerPolynomialZeroSet (p : ℕ) N
          (primeSubtype_ne_zero hprime p) polynomials) y).card ≤ D) :
    ((integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ d := by
  let hsubzero : (∏ p : P, (p : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ ↦ primeSubtype_ne_zero hprime p
  calc
    ((integerPolynomialZeroSet (primeProduct P) N
      (primeProduct_ne_zero fun p hp ↦ hprime p hp) polynomials).card : ℝ) =
        ((integerPolynomialZeroSet (∏ p : P, (p : ℕ)) N
          hsubzero polynomials).card : ℝ) := by
      exact_mod_cast card_integerPolynomialZeroSet_congr_modulus
        (primeSubtype_prod_eq_primeProduct P).symm
        (primeProduct_ne_zero fun p hp ↦ hprime p hp) hsubzero polynomials
    _ ≤ H ^ ε * (primeProduct P : ℝ) ^ d :=
      card_integerPolynomialZeroSet_squarefreeProduct_cast_le_rpow_mul_of_projection_fibers
        hM0 hε P hprime N d D hD hPcard hH polynomials coordinates hfibre

end

end TranslatedDepthSeven
