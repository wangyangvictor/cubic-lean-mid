import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Finite
import TranslatedDepthSeven.CharacteristicPolynomialAdjoinRoot

/-!
# Noether normalization and a literal generic triangular step

For a proper affine quotient over a field, Mathlib's Noether-normalization
theorem supplies an injective finite map from a polynomial ring.  The first
theorem below retains the useful bound on the number of normalization
parameters which is present in the quotient form of that theorem.

After extension from the normalization ring to its fraction field, the
coordinate algebra is finite free.  Multiplication by any selected element
therefore has a monic characteristic polynomial.  The last two theorems
record, without a presentation interface, the resulting vanishing equation
and the exact range of the corresponding `AdjoinRoot` map.  They are the
one-step statements which may be repeated for a literal finite list of
coordinates.

The normalization map supplied by Mathlib is polynomial, not asserted to be
linear in the original affine coordinates.  Likewise, these statements do
not bound the coefficients of the normalization map or of the characteristic
polynomials.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial
open scoped TensorProduct

universe u v w

/-- A finite strict chain of primes in the base of an integral extension can
be lifted, with the same length, once a prime over its first member has been
chosen.  Only the first and last contraction identities are retained because
they are all that is needed for the dimension comparison. -/
theorem exists_ltSeries_over_of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S]
    (l : LTSeries (PrimeSpectrum R)) (P : PrimeSpectrum S)
    (hP : P.asIdeal.comap (algebraMap R S) = l.head.asIdeal) :
    ∃ L : LTSeries (PrimeSpectrum S),
      L.length = l.length ∧ L.head = P ∧
        L.last.asIdeal.comap (algebraMap R S) = l.last.asIdeal := by
  induction l using RelSeries.inductionOn' generalizing P with
  | singleton p =>
      exact ⟨RelSeries.singleton _ P, rfl, by simp, by simpa using hP⟩
  | snoc l q hpq ih =>
      have hPhead : P.asIdeal.comap (algebraMap R S) = l.head.asIdeal := by
        simpa using hP
      obtain ⟨L, hlength, hhead, hlast⟩ := ih P hPhead
      letI : L.last.asIdeal.IsPrime := L.last.2
      letI : q.asIdeal.IsPrime := q.2
      have hcomap_le :
          L.last.asIdeal.comap (algebraMap R S) ≤ q.asIdeal := by
        rw [hlast]
        exact hpq.le
      obtain ⟨Q, hLQ, hQprime, hQcomap⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral
          q.asIdeal L.last.asIdeal hcomap_le
      let Q' : PrimeSpectrum S := ⟨Q, hQprime⟩
      have hLQstrict : L.last < Q' := by
        change L.last.asIdeal < Q
        refine lt_of_le_of_ne hLQ ?_
        intro hEq
        have hpq' : l.last < q := hpq
        apply hpq'.ne
        apply PrimeSpectrum.ext
        change l.last.asIdeal = q.asIdeal
        rw [← hlast, ← hQcomap, hEq]
      refine ⟨L.snoc Q' hLQstrict, ?_, ?_, ?_⟩
      · simp [hlength]
      · simp [hhead]
      · simpa [Q'] using hQcomap

/-- Contraction is strictly monotone on chains of primes in an integral
extension.  Hence the extension cannot have larger Krull dimension than its
base. -/
theorem ringKrullDim_le_of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  unfold ringKrullDim
  apply Order.krullDim_le_of_strictMono
    (fun P : PrimeSpectrum S ↦
      ⟨P.asIdeal.comap (algebraMap R S), inferInstance⟩)
  intro P Q hPQ
  change P.asIdeal.comap (algebraMap R S) <
    Q.asIdeal.comap (algebraMap R S)
  change P.asIdeal < Q.asIdeal at hPQ
  obtain ⟨hPQle, x, hxQ, hxP⟩ := SetLike.lt_iff_le_and_exists.mp hPQ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hPQle ⟨hxQ, hxP⟩
    (Algebra.IsIntegral.isIntegral x)

/-- An injective integral extension has the same Krull dimension.  The
reverse inequality is proved by lifting every finite strict chain with
`exists_ltSeries_over_of_isIntegral`; no dimension theorem is assumed. -/
theorem ringKrullDim_eq_of_isIntegral_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Nontrivial R] [Nontrivial S]
    [Algebra R S] [Algebra.IsIntegral R S]
    (hinjective : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm ringKrullDim_le_of_isIntegral
  change Order.krullDim (PrimeSpectrum R) ≤
    Order.krullDim (PrimeSpectrum S)
  rw [Order.krullDim_eq_iSup_length ( α := PrimeSpectrum R),
    Order.krullDim_eq_iSup_length ( α := PrimeSpectrum S)]
  norm_cast
  refine iSup_le fun (l : LTSeries (PrimeSpectrum R)) ↦ ?_
  obtain ⟨Q, -, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral
      l.head.asIdeal (⊥ : Ideal S) (by
        rw [Ideal.comap_bot_of_injective (algebraMap R S) hinjective]
        exact bot_le)
  let Q' : PrimeSpectrum S := ⟨Q, hQprime⟩
  obtain ⟨L, hlength, -, -⟩ :=
    exists_ltSeries_over_of_isIntegral l Q' hQcomap
  rw [← hlength]
  exact le_iSup (fun L : LTSeries (PrimeSpectrum S) ↦
    (L.length : ℕ∞)) L

/-- The unconditional numerical consequence currently obtainable for a
Noether normalization over a field: if the target has Krull dimension `d`,
then the number `s` of normalization parameters is at most `d`.

The converse inequality would follow from the exact formula
`dim k[X₁,…,Xₛ] = s`.  In the pinned Mathlib version that formula is the
unproved declaration
`MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing`, so it is not used
here. -/
theorem normalization_parameter_le_of_ringKrullDim_eq
    {k : Type u} [Field k] {s d : ℕ} {A : Type v}
    [CommRing A] [Nontrivial A] [Algebra k A]
    (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinjective : Function.Injective g) (hintegral : g.IsIntegral)
    (hdim : ringKrullDim A = d) :
    s ≤ d := by
  letI : Algebra (MvPolynomial (Fin s) k) A :=
    g.toRingHom.toAlgebra
  letI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A :=
    ⟨hintegral⟩
  have hdimension :
      ringKrullDim A = ringKrullDim (MvPolynomial (Fin s) k) :=
    ringKrullDim_eq_of_isIntegral_injective hinjective
  have hlower :=
    ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial
      (R := k) (Fin s)
  simp only [ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin] at hlower
  rw [← hdimension, hdim] at hlower
  exact_mod_cast hlower

/-- An injective integral polynomial subalgebra has exactly the expected
transcendence degree.  This identifies the number of normalization parameters
without using the unavailable polynomial-ring Krull-dimension formula. -/
theorem trdeg_eq_nat_of_integral_injective_polynomial
    {k A : Type u} [Field k] {s : ℕ}
    [CommRing A] [IsDomain A] [Algebra k A]
    (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinjective : Function.Injective g) (hintegral : g.IsIntegral) :
    Algebra.trdeg k A = (s : Cardinal) := by
  letI : Algebra (MvPolynomial (Fin s) k) A :=
    g.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      simp [RingHom.algebraMap_toAlgebra]
  letI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjective
  letI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A :=
    ⟨hintegral⟩
  have h := trdeg_add_eq k (MvPolynomial (Fin s) k) (A := A)
  simpa [trdeg_eq_zero, Cardinal.mk_fin] using h.symm

/-- Module-finite form of
`trdeg_eq_nat_of_integral_injective_polynomial`, matching the output of
Noether normalization. -/
theorem trdeg_eq_nat_of_finite_injective_polynomial
    {k A : Type u} [Field k] {s : ℕ}
    [CommRing A] [IsDomain A] [Algebra k A]
    (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinjective : Function.Injective g) (hfinite : g.Finite) :
    Algebra.trdeg k A = (s : Cardinal) :=
  trdeg_eq_nat_of_integral_injective_polynomial g hinjective
    hfinite.to_isIntegral

/-- If the transcendence degree of the target is displayed as the natural
number `d`, then an injective finite normalization in `s` variables forces
`s = d`. -/
theorem normalization_parameter_eq_of_trdeg_eq
    {k A : Type u} [Field k] {s d : ℕ}
    [CommRing A] [IsDomain A] [Algebra k A]
    (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinjective : Function.Injective g) (hfinite : g.Finite)
    (hdim : Algebra.trdeg k A = (d : Cardinal)) :
    s = d := by
  have hs :=
    trdeg_eq_nat_of_finite_injective_polynomial g hinjective hfinite
  have : (s : Cardinal) = (d : Cardinal) := hs.symm.trans hdim
  exact_mod_cast this

/-- A proper quotient of affine `n`-space admits an injective finite map from
a polynomial ring in at most `n` variables.  This is the module-finite form
of Mathlib's quotient version of Noether normalization. -/
theorem exists_finite_injective_normalization_of_affineQuotient
    {k : Type u} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    ∃ s ≤ n, ∃ g : MvPolynomial (Fin s) k →ₐ[k]
      (MvPolynomial (Fin n) k ⧸ I),
      Function.Injective g ∧ g.Finite := by
  obtain ⟨s, hs, g, hinjective, hintegral⟩ :=
    exists_integral_inj_algHom_of_quotient I hI
  have hcomp :
      algebraMap k (MvPolynomial (Fin n) k ⧸ I) =
        g.toRingHom.comp (algebraMap k (MvPolynomial (Fin s) k)) := by
    algebraize [g.toRingHom]
    rw [IsScalarTower.algebraMap_eq k (MvPolynomial (Fin s) k),
      RingHom.algebraMap_toAlgebra']
  have hfinite : g.Finite :=
    hintegral.to_finite
      ((hcomp ▸
        RingHom.finiteType_algebraMap.mpr
          (inferInstance : Algebra.FiniteType k
            (MvPolynomial (Fin n) k ⧸ I))).of_comp_finiteType)
  exact ⟨s, hs, g, hinjective, hfinite⟩

/-- Prime-affine specialization of
`exists_finite_injective_normalization_of_affineQuotient`.  The quotient is
an integral domain by the existing quotient instance. -/
theorem exists_finite_injective_normalization_of_primeAffine
    {k : Type u} [Field k] {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] :
    ∃ s ≤ n, ∃ g : MvPolynomial (Fin s) k →ₐ[k]
      (MvPolynomial (Fin n) k ⧸ P),
      Function.Injective g ∧ g.Finite :=
  exists_finite_injective_normalization_of_affineQuotient P
    (inferInstance : P.IsPrime).ne_top

/-- The prime-affine normalization together with the exact transcendence-
degree identification of its parameter count. -/
theorem exists_finite_injective_normalization_of_primeAffine_with_trdeg
    {k : Type u} [Field k] {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] :
    ∃ s ≤ n, ∃ g : MvPolynomial (Fin s) k →ₐ[k]
      (MvPolynomial (Fin n) k ⧸ P),
      Function.Injective g ∧ g.Finite ∧
        Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ P) =
          (s : Cardinal) := by
  obtain ⟨s, hs, g, hinjective, hfinite⟩ :=
    exists_finite_injective_normalization_of_primeAffine P
  exact ⟨s, hs, g, hinjective, hfinite,
    trdeg_eq_nat_of_finite_injective_polynomial g hinjective hfinite⟩

/-- If a prime affine algebra has displayed transcendence degree `d`, its
Noether normalization may be stated directly with a polynomial base in
exactly `d` variables.  This is the form needed for a `p^d` finite-field
base count. -/
theorem exists_finite_injective_normalization_of_primeAffine_of_trdeg_eq
    {k : Type u} [Field k] {n d : ℕ}
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (htrdeg : Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ P) =
      (d : Cardinal)) :
    ∃ g : MvPolynomial (Fin d) k →ₐ[k]
      (MvPolynomial (Fin n) k ⧸ P),
      Function.Injective g ∧ g.Finite := by
  obtain ⟨s, -, g, hinjective, hfinite⟩ :=
    exists_finite_injective_normalization_of_primeAffine P
  have hsd :=
    normalization_parameter_eq_of_trdeg_eq
      g hinjective hfinite htrdeg
  subst s
  exact ⟨g, hinjective, hfinite⟩

/-- A finite module over a Noetherian domain becomes free after inverting one
explicitly existential nonzero element of the base.  Applied to the finite
map returned by Noether normalization, this is the available generic-freeness
step on one principal open. -/
theorem exists_nonzero_principal_localization_free
    {B : Type u} {A : Type v}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [CommRing A] [Algebra B A] [Module.Finite B A] :
    ∃ h : B, h ≠ 0 ∧
      Module.Free (Localization (Submonoid.powers h))
        (LocalizedModule (Submonoid.powers h) A) ∧
      Module.finrank (Localization (Submonoid.powers h))
          (LocalizedModule (Submonoid.powers h) A) =
        Module.finrank (FractionRing B)
          (LocalizedModule (nonZeroDivisors B) A) := by
  letI : Module.FinitePresentation B A :=
    Module.finitePresentation_of_finite B A
  obtain ⟨h, hh, hfree, hrank⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      (nonZeroDivisors B)
      (LocalizedModule.mkLinearMap (nonZeroDivisors B) A)
      (FractionRing B)
  exact ⟨h, mem_nonZeroDivisors_iff_ne_zero.mp hh, hfree, hrank⟩

/-- On the generic fibre of a finite algebra over a domain, every selected
element satisfies the characteristic polynomial of its multiplication map.
The equation is monic and its degree is exactly the generic module rank. -/
theorem genericFibre_lmul_charpoly_relation
    {B : Type u} {A : Type v}
    [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    [Module.Finite B A] (x : A) :
    ∃ f : (FractionRing B)[X],
      f.Monic ∧
      f.natDegree =
        Module.finrank (FractionRing B)
          (FractionRing B ⊗[B] A) ∧
      Polynomial.aeval
          (Algebra.TensorProduct.includeRight x :
            FractionRing B ⊗[B] A) f = 0 := by
  letI : Module.Finite (FractionRing B) (FractionRing B ⊗[B] A) :=
    Module.Finite.base_change B (FractionRing B) A
  let xK : FractionRing B ⊗[B] A :=
    Algebra.TensorProduct.includeRight x
  let f : (FractionRing B)[X] :=
    (Algebra.lmul (FractionRing B) (FractionRing B ⊗[B] A) xK).charpoly
  refine ⟨f, lmul_charpoly_monic xK, lmul_charpoly_natDegree xK, ?_⟩
  exact aeval_lmul_charpoly_eq_zero xK

/-- The characteristic-polynomial relation from the preceding theorem gives
a literal one-step monic triangular presentation.  Its image is exactly the
subalgebra generated by the selected generic-fibre coordinate. -/
theorem genericFibre_lmul_charpoly_adjoinRoot_range
    {B : Type u} {A : Type v}
    [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    [Module.Finite B A] (x : A) :
    let xK : FractionRing B ⊗[B] A :=
      Algebra.TensorProduct.includeRight x
    let f : (FractionRing B)[X] :=
      (Algebra.lmul (FractionRing B) (FractionRing B ⊗[B] A) xK).charpoly
    (AdjoinRoot.liftAlgHom f
      (Algebra.ofId (FractionRing B) (FractionRing B ⊗[B] A))
      xK (aeval_lmul_charpoly_eq_zero xK)).range =
      Algebra.adjoin (FractionRing B) ({xK} : Set (FractionRing B ⊗[B] A)) := by
  letI : Module.Finite (FractionRing B) (FractionRing B ⊗[B] A) :=
    Module.Finite.base_change B (FractionRing B) A
  dsimp only
  exact range_adjoinRoot_liftAlgHom_eq_adjoin_singleton _ _ _

/-- Relative form of the generic triangular step.  Given any previous
`K`-algebra stage mapping to the generic fibre, mapping the same characteristic
polynomial into that stage and adjoining the selected root enlarges the range
by exactly that coordinate. -/
theorem genericFibre_relative_lmul_charpoly_step
    {B : Type u} {A : Type v} {T : Type w}
    [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    [Module.Finite B A]
    [CommRing T] [Nontrivial T] [Algebra (FractionRing B) T]
    (phi : T →ₐ[FractionRing B] (FractionRing B ⊗[B] A)) (x : A) :
    let xK : FractionRing B ⊗[B] A :=
      Algebra.TensorProduct.includeRight x
    let f : T[X] :=
      ((Algebra.lmul (FractionRing B) (FractionRing B ⊗[B] A) xK).charpoly).map
        (algebraMap (FractionRing B) T)
    f.Monic ∧
      f.natDegree =
        Module.finrank (FractionRing B) (FractionRing B ⊗[B] A) ∧
      f.eval₂ phi xK = 0 ∧
      (AdjoinRoot.liftAlgHom f phi xK
        (eval₂_map_lmul_charpoly_eq_zero phi xK)).range =
        phi.range ⊔
          Algebra.adjoin (FractionRing B)
            ({xK} : Set (FractionRing B ⊗[B] A)) := by
  letI : Module.Finite (FractionRing B) (FractionRing B ⊗[B] A) :=
    Module.Finite.base_change B (FractionRing B) A
  dsimp only
  exact ⟨map_lmul_charpoly_monic _, map_lmul_charpoly_natDegree _,
    eval₂_map_lmul_charpoly_eq_zero phi _,
    range_adjoinRoot_lmulCharpoly_liftAlgHom phi _⟩

end

end TranslatedDepthSeven
