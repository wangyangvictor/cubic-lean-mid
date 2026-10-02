import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Rank bounds for one monic triangular extension

An exact monic triangular presentation is built one variable at a time.  This
file proves the one-step statement needed for that induction.  If `S` has a
finite basis over a field `K` and `f : S[X]` is monic, then adjoining one root
of `f` multiplies the `K`-dimension by `deg f`.  Any further quotient has no
larger `K`-dimension.

Iterating this theorem gives the product of the successive monic degrees.  No
Bézout theorem, generic slice, component theorem, or external axiom is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial
open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {ι : Type w}

/-- The explicit `R`-basis of a one-step monic extension, obtained by
combining a basis of `S/R` with the power basis of `AdjoinRoot f/S`.  This
works over an arbitrary commutative bottom ring, which is the form needed
before taking a fibre of a triangular presentation. -/
def monicAdjoinRootTowerBasis
    (b : Module.Basis ι R S) {f : S[X]} (hf : f.Monic) :
    Module.Basis (ι × Fin f.natDegree) R (AdjoinRoot f) :=
  b.smulTower (AdjoinRoot.powerBasis' hf).basis

/-- A one-step monic triangular extension is free over the bottom ring, on
the explicit product basis above. -/
theorem free_monicAdjoinRoot_of_basis
    (b : Module.Basis ι R S) {f : S[X]} (hf : f.Monic) :
    Module.Free R (AdjoinRoot f) :=
  Module.Free.of_basis (monicAdjoinRootTowerBasis b hf)

/-- With a finite lower basis, the one-step monic triangular extension is
also finite over the bottom ring. -/
theorem finite_monicAdjoinRoot_of_basis
    [Fintype ι] (b : Module.Basis ι R S) {f : S[X]} (hf : f.Monic) :
    Module.Finite R (AdjoinRoot f) :=
  Module.Finite.of_basis (monicAdjoinRootTowerBasis b hf)

section Field

variable {K : Type u} [Field K]

/-- An arbitrary exact finite free presentation remains free of the same
rank after specializing the base ring to a field.  In the determinant-method
application `R` is the coordinate ring of the chosen linear projection,
`K` is the residue field of a point of the target, and `S` is the exact
triangular coordinate algebra. -/
theorem finrank_baseChange_eq_card
    {A : Type v} [CommRing A] [Algebra R A]
    [Fintype ι] (b : Module.Basis ι R A) [Algebra R K] :
    Module.finrank K (K ⊗[R] A) = Fintype.card ι := by
  rw [Module.finrank_eq_card_basis (b.baseChange K)]

/-- A specialization of a positive-rank finite free presentation is not the
zero ring.  This is the fibrewise nonemptiness statement in its most direct
algebraic form; it needs no genericity hypothesis. -/
theorem nontrivial_baseChange_of_nonempty_basis
    {A : Type v} [CommRing A] [Algebra R A]
    (b : Module.Basis ι R A) [Algebra R K] [Nonempty ι] :
    Nontrivial (K ⊗[R] A) := by
  let bK : Module.Basis ι K (K ⊗[R] A) := b.baseChange K
  let i : ι := Classical.choice inferInstance
  exact ⟨⟨0, bK i, (bK.ne_zero i).symm⟩⟩

variable [Fintype ι]

/-- Lying over for the exact finite free presentation.  A positive-rank
triangular tower has a prime above every prime of the projection base. -/
theorem exists_prime_lyingOver_of_nonempty_basis
    {A : Type v} [CommRing A] [Algebra R A] [Nontrivial R]
    (b : Module.Basis ι R A) [Nonempty ι]
    (P : Ideal R) [P.IsPrime] :
    ∃ Q : Ideal A, Q.IsPrime ∧ Q.comap (algebraMap R A) = P := by
  letI : Nontrivial A := by
    let i : ι := Classical.choice inferInstance
    exact ⟨⟨0, b i, (b.ne_zero i).symm⟩⟩
  letI : Module.Free R A := Module.Free.of_basis b
  letI : Module.Finite R A := Module.Finite.of_basis b
  obtain ⟨Q, -, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal A) (by
      change RingHom.ker (algebraMap R A) ≤ P
      rw [FaithfulSMul.ker_algebraMap_eq_bot]
      exact bot_le)
  exact ⟨Q, hQprime, hQcomap⟩

/-- Every closed subscheme of a fibre of an exact finite free presentation
has vector-space dimension at most the rank of that presentation.  The ideal
`I` permits additional equations after the triangular equations; these can
only decrease the fibre length. -/
theorem finrank_baseChange_quotient_le_card
    {A : Type v} [CommRing A] [Algebra R A]
    (b : Module.Basis ι R A) [Algebra R K]
    (I : Ideal (K ⊗[R] A)) :
    Module.finrank K ((K ⊗[R] A) ⧸ I) ≤ Fintype.card ι := by
  let bK : Module.Basis ι K (K ⊗[R] A) := b.baseChange K
  letI : Module.Free K (K ⊗[R] A) := Module.Free.of_basis bK
  letI : Module.Finite K (K ⊗[R] A) := Module.Finite.of_basis bK
  let q : (K ⊗[R] A) →ₗ[K] (K ⊗[R] A) ⧸ I :=
    (Ideal.Quotient.mkₐ K I).toLinearMap
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective K I
  have hrange : LinearMap.range q = ⊤ := LinearMap.range_eq_top.mpr hq
  calc
    Module.finrank K ((K ⊗[R] A) ⧸ I) =
        Module.finrank K (LinearMap.range q) := by rw [hrange]; simp
    _ ≤ Module.finrank K (K ⊗[R] A) := LinearMap.finrank_range_le q
    _ = Fintype.card ι := finrank_baseChange_eq_card b

/-- Scheme-theoretic version of `finrank_baseChange_quotient_le_card`.
Thus a linear-section fibre of an exact monic triangular presentation has
length at most the product of the successive monic degrees. -/
theorem length_baseChange_quotient_le_card
    {A : Type v} [CommRing A] [Algebra R A]
    (b : Module.Basis ι R A) [Algebra R K]
    (I : Ideal (K ⊗[R] A)) :
    Module.length K ((K ⊗[R] A) ⧸ I) ≤ (Fintype.card ι : ℕ∞) := by
  let bK : Module.Basis ι K (K ⊗[R] A) := b.baseChange K
  letI : Module.Free K (K ⊗[R] A) := Module.Free.of_basis bK
  letI : Module.Finite K (K ⊗[R] A) := Module.Finite.of_basis bK
  rw [Module.length_eq_finrank]
  exact_mod_cast finrank_baseChange_quotient_le_card b I

/-- The form used for a component coordinate ring.  Exact equality with the
triangular algebra is unnecessary: if the component algebra is any quotient
`A ⧸ J` of a finite free algebra `A`, then every field-valued linear-section
fibre has dimension at most the rank of `A`.  Tensor-product right exactness
is the only fact needed to pass the quotient through specialization. -/
theorem finrank_baseChange_quotientAlgebra_le_card
    {A : Type v} [CommRing A] [Algebra R A]
    (b : Module.Basis ι R A) [Algebra R K]
    (J : Ideal A) :
    Module.finrank K (K ⊗[R] (A ⧸ J)) ≤ Fintype.card ι := by
  let bK : Module.Basis ι K (K ⊗[R] A) := b.baseChange K
  letI : Module.Free K (K ⊗[R] A) := Module.Free.of_basis bK
  letI : Module.Finite K (K ⊗[R] A) := Module.Finite.of_basis bK
  let qR : A →ₗ[R] A ⧸ J := (Ideal.Quotient.mkₐ R J).toLinearMap
  let qK : (K ⊗[R] A) →ₗ[K] (K ⊗[R] (A ⧸ J)) := qR.baseChange K
  have hqR : Function.Surjective qR := Ideal.Quotient.mkₐ_surjective R J
  have hqK : Function.Surjective qK := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective K hqR
  have hrange : LinearMap.range qK = ⊤ := LinearMap.range_eq_top.mpr hqK
  calc
    Module.finrank K (K ⊗[R] (A ⧸ J)) =
        Module.finrank K (LinearMap.range qK) := by rw [hrange]; simp
    _ ≤ Module.finrank K (K ⊗[R] A) := LinearMap.finrank_range_le qK
    _ = Fintype.card ι := finrank_baseChange_eq_card b

/-- Scheme-theoretic fibre-length version for a quotient component algebra.
This is the exact upper bound needed after a linear projection. -/
theorem length_baseChange_quotientAlgebra_le_card
    {A : Type v} [CommRing A] [Algebra R A]
    (b : Module.Basis ι R A) [Algebra R K]
    (J : Ideal A) :
    Module.length K (K ⊗[R] (A ⧸ J)) ≤ (Fintype.card ι : ℕ∞) := by
  let bK : Module.Basis ι K (K ⊗[R] A) := b.baseChange K
  letI : Module.Finite K (K ⊗[R] A) := Module.Finite.of_basis bK
  let qR : A →ₗ[R] A ⧸ J := (Ideal.Quotient.mkₐ R J).toLinearMap
  let qK : (K ⊗[R] A) →ₗ[K] (K ⊗[R] (A ⧸ J)) := qR.baseChange K
  have hqR : Function.Surjective qR := Ideal.Quotient.mkₐ_surjective R J
  have hqK : Function.Surjective qK := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective K hqR
  letI : Module.Finite K (K ⊗[R] (A ⧸ J)) :=
    Module.Finite.of_surjective qK hqK
  rw [Module.length_eq_finrank]
  exact_mod_cast finrank_baseChange_quotientAlgebra_le_card b J

/-- One triangular step, specialization, and passage to a quotient, combined
in the exact numerical form used in an iterated triangular presentation. -/
theorem length_baseChange_quotient_monicAdjoinRoot_le
    (b : Module.Basis ι R S) {f : S[X]} (hf : f.Monic)
    [Algebra R K] (J : Ideal (AdjoinRoot f)) :
    Module.length K (K ⊗[R] (AdjoinRoot f ⧸ J)) ≤
      (Fintype.card ι * f.natDegree : ℕ∞) := by
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using
    length_baseChange_quotientAlgebra_le_card
      (monicAdjoinRootTowerBasis b hf) J

/-- Vector-space-dimension form of
`length_baseChange_quotient_monicAdjoinRoot_le`. -/
theorem finrank_baseChange_quotient_monicAdjoinRoot_le
    (b : Module.Basis ι R S) {f : S[X]} (hf : f.Monic)
    [Algebra R K] (J : Ideal (AdjoinRoot f)) :
    Module.finrank K (K ⊗[R] (AdjoinRoot f ⧸ J)) ≤
      Fintype.card ι * f.natDegree := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    finrank_baseChange_quotientAlgebra_le_card
      (monicAdjoinRootTowerBasis b hf) J

variable [Algebra K S]

/-- Adjoining a root of a monic polynomial multiplies the dimension over the
bottom field by the degree of that polynomial. -/
theorem finrank_monicAdjoinRoot_eq
    (b : Module.Basis ι K S) {f : S[X]} (hf : f.Monic) :
    Module.finrank K (AdjoinRoot f) =
      Fintype.card ι * f.natDegree := by
  rw [Module.finrank_eq_card_basis (monicAdjoinRootTowerBasis b hf)]
  simp only [Fintype.card_prod, Fintype.card_fin]

/-- A quotient of a one-step monic extension has dimension at most the
product supplied by the triangular basis.  Scheme-theoretically, after a
base point is fixed this is the required upper bound for the length of any
zero-dimensional fibre presented as such a quotient. -/
theorem finrank_quotient_monicAdjoinRoot_le
    (b : Module.Basis ι K S) {f : S[X]} (hf : f.Monic)
    (I : Ideal (AdjoinRoot f)) :
    Module.finrank K (AdjoinRoot f ⧸ I) ≤
      Fintype.card ι * f.natDegree := by
  letI : Module.Free K S := Module.Free.of_basis b
  letI : Module.Finite K S := Module.Finite.of_basis b
  letI : Module.Free S (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite S (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.Free K (AdjoinRoot f) :=
    Module.Free.trans (R := K) (S := S) (M := AdjoinRoot f)
  letI : Module.Finite K (AdjoinRoot f) :=
    Module.Finite.trans (R := K) S (AdjoinRoot f)
  let q : AdjoinRoot f →ₗ[K] AdjoinRoot f ⧸ I :=
    (Ideal.Quotient.mkₐ K I).toLinearMap
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective K I
  have hrange : LinearMap.range q = ⊤ := LinearMap.range_eq_top.mpr hq
  calc
    Module.finrank K (AdjoinRoot f ⧸ I) =
        Module.finrank K (LinearMap.range q) := by rw [hrange]; simp
    _ ≤ Module.finrank K (AdjoinRoot f) := LinearMap.finrank_range_le q
    _ = Fintype.card ι * f.natDegree := finrank_monicAdjoinRoot_eq b hf

/-- The same quotient bound stated as scheme-theoretic fibre length.  Over a
field, module length equals vector-space dimension. -/
theorem length_quotient_monicAdjoinRoot_le
    (b : Module.Basis ι K S) {f : S[X]} (hf : f.Monic)
    (I : Ideal (AdjoinRoot f)) :
    Module.length K (AdjoinRoot f ⧸ I) ≤
      (Fintype.card ι * f.natDegree : ℕ∞) := by
  letI : Module.Free K S := Module.Free.of_basis b
  letI : Module.Finite K S := Module.Finite.of_basis b
  letI : Module.Free S (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite S (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.Free K (AdjoinRoot f) :=
    Module.Free.trans (R := K) (S := S) (M := AdjoinRoot f)
  letI : Module.Finite K (AdjoinRoot f) :=
    Module.Finite.trans (R := K) S (AdjoinRoot f)
  rw [Module.length_eq_finrank]
  exact_mod_cast finrank_quotient_monicAdjoinRoot_le b hf I

/-- The base case used when iterating the preceding theorem. -/
theorem finrank_baseField_eq_one : Module.finrank K K = 1 := by
  simp

end Field

end

end TranslatedDepthSeven
