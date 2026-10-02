import TranslatedDepthSeven.StandardSmoothJetComparison
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Smooth.Basic

/-!
# Higher jets at a standard-smooth rational point

This file compares the finite infinitesimal neighbourhood of a rational
standard-smooth point with the corresponding neighbourhood of the origin in
affine space.  The comparison is made by explicit algebra maps and the
elementary nilpotent-filtration lemma from
`NilpotentCotangentSurjectivity`; no regular-local or Hilbert--Samuel theorem
is used.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v w

variable {K : Type u} [Field K]

/-- The `k`-th finite infinitesimal neighbourhood of an augmented algebra.
Our indexing agrees with Hilbert--Samuel functions: the defining ideal is
the `(k+1)`-st power. -/
abbrev augmentedJet {B : Type v} [CommRing B] [Algebra K B]
    (f : B →ₐ[K] K) (k : ℕ) :=
  B ⧸ RingHom.ker f.toRingHom ^ (k + 1)

/-- Evaluation on an augmented jet. -/
noncomputable def augmentedJetEvaluation
    {B : Type v} [CommRing B] [Algebra K B]
    (f : B →ₐ[K] K) (k : ℕ) : augmentedJet f k →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ f fun x hx ↦
    show f x = 0 from Ideal.pow_le_self (Nat.succ_ne_zero k) hx

@[simp]
theorem augmentedJetEvaluation_mk
    {B : Type v} [CommRing B] [Algebra K B]
    (f : B →ₐ[K] K) (k : ℕ) (x : B) :
    augmentedJetEvaluation f k (Ideal.Quotient.mk _ x) = f x :=
  rfl

/-- A morphism respecting augmentations induces a morphism of every finite
infinitesimal neighbourhood. -/
noncomputable def augmentedJetMap
    {B : Type v} {C : Type w} [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C]
    (fB : B →ₐ[K] K) (fC : C →ₐ[K] K) (g : B →ₐ[K] C)
    (hcomp : fC.comp g = fB) (k : ℕ) :
    augmentedJet fB k →ₐ[K] augmentedJet fC k := by
  let IB : Ideal B := RingHom.ker fB.toRingHom
  let IC : Ideal C := RingHom.ker fC.toRingHom
  have hI : IB ≤ IC.comap g := by
    intro x hx
    change fC (g x) = 0
    rw [← AlgHom.comp_apply, hcomp]
    exact hx
  exact Ideal.quotientMapₐ (IC ^ (k + 1)) g
    ((Ideal.pow_right_mono hI (k + 1)).trans (Ideal.le_comap_pow g (k + 1)))

@[simp]
theorem augmentedJetMap_mk
    {B : Type v} {C : Type w} [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C]
    (fB : B →ₐ[K] K) (fC : C →ₐ[K] K) (g : B →ₐ[K] C)
    (hcomp : fC.comp g = fB) (k : ℕ) (x : B) :
    augmentedJetMap fB fC g hcomp k (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (g x) :=
  rfl

/-- The map on jets respects the induced augmentations. -/
theorem comp_augmentedJetMap
    {B : Type v} {C : Type w} [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C]
    (fB : B →ₐ[K] K) (fC : C →ₐ[K] K) (g : B →ₐ[K] C)
    (hcomp : fC.comp g = fB) (k : ℕ) :
    (augmentedJetEvaluation fC k).comp
        (augmentedJetMap fB fC g hcomp k) =
      augmentedJetEvaluation fB k := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro x
  change augmentedJetEvaluation fC k
      (augmentedJetMap fB fC g hcomp k (Ideal.Quotient.mk _ x)) =
    augmentedJetEvaluation fB k (Ideal.Quotient.mk _ x)
  rw [augmentedJetMap_mk, augmentedJetEvaluation_mk,
    augmentedJetEvaluation_mk]
  exact AlgHom.congr_fun hcomp x

/-- The augmentation ideal of a finite jet is the image of the original
augmentation ideal. -/
theorem ker_augmentedJetEvaluation
    {B : Type v} [CommRing B] [Algebra K B]
    (f : B →ₐ[K] K) (k : ℕ) :
    RingHom.ker (augmentedJetEvaluation f k).toRingHom =
      (RingHom.ker f.toRingHom).map
        (Ideal.Quotient.mk (RingHom.ker f.toRingHom ^ (k + 1))) := by
  exact Ideal.ker_quotient_lift f.toRingHom
    (Ideal.pow_le_self (Nat.succ_ne_zero k))

/-- The augmentation ideal in the `k`-th jet has vanishing `(k+1)`-st
power. -/
theorem pow_ker_augmentedJetEvaluation_eq_bot
    {B : Type v} [CommRing B] [Algebra K B]
    (f : B →ₐ[K] K) (k : ℕ) :
    RingHom.ker (augmentedJetEvaluation f k).toRingHom ^ (k + 1) = ⊥ := by
  rw [ker_augmentedJetEvaluation, ← Ideal.map_pow,
    Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

/-! ## The polynomial-coordinate map -/

/-- The chosen smooth coordinates induce a map from the truncated
polynomial algebra to the jet at the smooth point. -/
noncomputable def smoothCoordinateJetMap
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    augmentedJet (polynomialOriginAugmentation (K := K) r) k →ₐ[K]
      augmentedJet f k :=
  augmentedJetMap (polynomialOriginAugmentation r) f
    (smoothCoordinateMap f r)
    (comp_smoothCoordinateMap_eq_polynomialOriginAugmentation f r) k

/-- The polynomial-coordinate map respects the induced rational-point
evaluations. -/
theorem comp_smoothCoordinateJetMap_evaluation
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    (augmentedJetEvaluation f k).comp (smoothCoordinateJetMap f r k) =
      augmentedJetEvaluation (polynomialOriginAugmentation (K := K) r) k :=
  comp_augmentedJetMap (polynomialOriginAugmentation r) f
    (smoothCoordinateMap f r)
    (comp_smoothCoordinateMap_eq_polynomialOriginAugmentation f r) k

/-- The coordinate map is onto every finite jet.  The only input is the
literal first-order approximation by the chosen cotangent basis. -/
theorem smoothCoordinateJetMap_surjective
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    Function.Surjective (smoothCoordinateJetMap f r k) := by
  let e := polynomialOriginAugmentation (K := K) r
  let g := smoothCoordinateJetMap f r k
  let eP := augmentedJetEvaluation e k
  let eA := augmentedJetEvaluation f k
  apply TranslatedDepthSeven.AlgHom.surjective_of_augmented_firstOrder_of_pow_ker_eq_bot
      g eP eA
      (comp_augmentedJetMap e f (smoothCoordinateMap f r)
        (comp_smoothCoordinateMap_eq_polynomialOriginAugmentation f r) k)
      k (pow_ker_augmentedJetEvaluation_eq_bot f k)
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ha : a ∈ RingHom.ker f.toRingHom := by
    change f a = 0
    simpa [eA, augmentedJetEvaluation] using hx
  obtain ⟨p, hp, hap⟩ := smoothCoordinateMap_firstOrder_approximation f r a ha
  refine ⟨Ideal.Quotient.mk _ p, ?_, ?_⟩
  · change eP (Ideal.Quotient.mk _ p) = 0
    simpa [eP] using hp
  · change Ideal.Quotient.mk _ a -
      Ideal.Quotient.mk _ (smoothCoordinateMap f r p) ∈
        RingHom.ker eA.toRingHom ^ 2
    rw [← map_sub]
    rw [ker_augmentedJetEvaluation, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hap

/-- The first jet of the origin in affine `r`-space has dimension `r+1`. -/
theorem finrank_polynomialOrigin_firstJet_eq_add_one (r : ℕ) :
    Module.finrank K
      (augmentedJet (polynomialOriginAugmentation (K := K) r) 1) = r + 1 := by
  change Module.finrank K
    (MvPolynomial (Fin r) K ⧸
      RingHom.ker
        (MvPolynomial.constantCoeff : MvPolynomial (Fin r) K →+* K) ^ (1 + 1)) =
    r + 1
  rw [finrank_originPowerQuotient_eq_choose]
  simp [Nat.add_comm, Nat.choose_succ_self_right]

/-- The map determined by a cotangent basis is an isomorphism on first
jets. -/
theorem smoothCoordinateJetMap_first_bijective
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    Function.Bijective (smoothCoordinateJetMap f r 1) := by
  let e := polynomialOriginAugmentation (K := K) r
  let P₁ := augmentedJet e 1
  let A₁ := augmentedJet f 1
  let E := originPowerQuotientLinearEquivRestrictTotalDegree K r 1
  letI : Module.Finite K (MvPolynomial.restrictTotalDegree (Fin r) K 1) :=
    inferInstance
  letI : Module.Finite K P₁ := Module.Finite.equiv E.symm
  letI : Module.Finite K (RingHom.ker f.toRingHom).Cotangent :=
    cotangent_moduleFinite_of_isStandardSmoothOfRelativeDimension f r
  letI : Module.Finite K A₁ := firstJet_moduleFinite_of_cotangent f
  have hdim : Module.finrank K P₁ = Module.finrank K A₁ := by
    rw [show Module.finrank K P₁ = r + 1 by
      exact finrank_polynomialOrigin_firstJet_eq_add_one r]
    exact (finrank_firstJet_eq_add_one_of_isStandardSmoothOfRelativeDimension f r).symm
  have hsurj : Function.Surjective (smoothCoordinateJetMap f r 1) :=
    smoothCoordinateJetMap_surjective f r 1
  have hinj : Function.Injective (smoothCoordinateJetMap f r 1) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (smoothCoordinateJetMap f r 1).toLinearMap)).2 hsurj
  exact ⟨hinj, hsurj⟩

/-- In every positive-order jet, the kernel of the coordinate map begins in
degree two.  This is the precise first-order fact needed for the reverse
nilpotent-filtration argument. -/
theorem ker_smoothCoordinateJetMap_le_square
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    RingHom.ker (smoothCoordinateJetMap f r k).toRingHom ≤
      RingHom.ker
        (augmentedJetEvaluation
          (polynomialOriginAugmentation (K := K) r) k).toRingHom ^ 2 := by
  let e := polynomialOriginAugmentation (K := K) r
  intro y hy
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hcoord : smoothCoordinateMap f r p ∈
      RingHom.ker f.toRingHom ^ (k + 1) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [smoothCoordinateJetMap] using hy
  have hcoord₂ : smoothCoordinateMap f r p ∈
      RingHom.ker f.toRingHom ^ 2 :=
    Ideal.pow_le_pow_right (show 2 ≤ k + 1 by omega) hcoord
  have hzero : smoothCoordinateJetMap f r 1 (Ideal.Quotient.mk _ p) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hcoord₂
  have hpzero : (Ideal.Quotient.mk
      (RingHom.ker e.toRingHom ^ (1 + 1))) p = 0 :=
    (smoothCoordinateJetMap_first_bijective f r).1 hzero
  have hp : p ∈ RingHom.ker e.toRingHom ^ 2 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hpzero)
  rw [ker_augmentedJetEvaluation, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hp

/-- The kernel of the coordinate map on a positive-order jet is
nilpotent. -/
theorem isNilpotent_ker_smoothCoordinateJetMap
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    IsNilpotent (RingHom.ker (smoothCoordinateJetMap f r k).toRingHom) := by
  let eP := augmentedJetEvaluation
    (polynomialOriginAugmentation (K := K) r) k
  have hker : RingHom.ker (smoothCoordinateJetMap f r k).toRingHom ≤
      RingHom.ker eP.toRingHom :=
    (ker_smoothCoordinateJetMap_le_square f r k hk).trans
      (Ideal.pow_le_self two_ne_zero)
  refine ⟨k + 1, le_antisymm ?_ bot_le⟩
  exact (Ideal.pow_right_mono hker (k + 1)).trans
    (le_of_eq (pow_ker_augmentedJetEvaluation_eq_bot
      (polynomialOriginAugmentation (K := K) r) k))

/-! ## A reverse map supplied by formal smoothness -/

/-- Lift the quotient map from the smooth algebra through the surjective
polynomial-coordinate map. -/
noncomputable def smoothCoordinateJetLift
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    A →ₐ[K] augmentedJet (polynomialOriginAugmentation (K := K) r) k := by
  letI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth r
  letI : Algebra.FormallySmooth K A := inferInstance
  exact Algebra.FormallySmooth.liftOfSurjective
    (Ideal.Quotient.mkₐ K (RingHom.ker f.toRingHom ^ (k + 1)))
    (smoothCoordinateJetMap f r k)
    (smoothCoordinateJetMap_surjective f r k)
    (isNilpotent_ker_smoothCoordinateJetMap f r k hk)

/-- The lifted map is a section of the coordinate map before descending
the source modulo its augmentation ideal. -/
theorem comp_smoothCoordinateJetLift
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    (smoothCoordinateJetMap f r k).comp
        (smoothCoordinateJetLift f r k hk) =
      Ideal.Quotient.mkₐ K (RingHom.ker f.toRingHom ^ (k + 1)) := by
  letI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth r
  letI : Algebra.FormallySmooth K A := inferInstance
  exact Algebra.FormallySmooth.comp_liftOfSurjective
    (Ideal.Quotient.mkₐ K (RingHom.ker f.toRingHom ^ (k + 1)))
    (smoothCoordinateJetMap f r k)
    (smoothCoordinateJetMap_surjective f r k)
    (isNilpotent_ker_smoothCoordinateJetMap f r k hk)

/-- The formal-smooth lift respects the rational augmentations. -/
theorem comp_smoothCoordinateJetLift_evaluation
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    (augmentedJetEvaluation
      (polynomialOriginAugmentation (K := K) r) k).comp
        (smoothCoordinateJetLift f r k hk) = f := by
  apply AlgHom.ext
  intro x
  calc
    augmentedJetEvaluation (polynomialOriginAugmentation r) k
        (smoothCoordinateJetLift f r k hk x) =
      augmentedJetEvaluation f k
        (smoothCoordinateJetMap f r k
          (smoothCoordinateJetLift f r k hk x)) := by
            exact (AlgHom.congr_fun
              (comp_smoothCoordinateJetMap_evaluation f r k)
              (smoothCoordinateJetLift f r k hk x)).symm
    _ = augmentedJetEvaluation f k
        (Ideal.Quotient.mk _ x) := by
          congr 1
          exact AlgHom.congr_fun (comp_smoothCoordinateJetLift f r k hk) x
    _ = f x := augmentedJetEvaluation_mk f k x

/-- The lift annihilates the `(k+1)`-st power of the point ideal, hence
descends to the finite jet. -/
theorem smoothCoordinateJetLift_pow_eq_zero
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A]
    (x : A) (hx : x ∈ RingHom.ker f.toRingHom ^ (k + 1)) :
    smoothCoordinateJetLift f r k hk x = 0 := by
  let eP := augmentedJetEvaluation
    (polynomialOriginAugmentation (K := K) r) k
  have hI : RingHom.ker f.toRingHom ≤
      (RingHom.ker eP.toRingHom).comap
        (smoothCoordinateJetLift f r k hk) := by
    intro y hy
    change eP (smoothCoordinateJetLift f r k hk y) = 0
    rw [← AlgHom.comp_apply, comp_smoothCoordinateJetLift_evaluation]
    exact hy
  have hx' : smoothCoordinateJetLift f r k hk x ∈
      RingHom.ker eP.toRingHom ^ (k + 1) :=
    ((Ideal.pow_right_mono hI (k + 1)).trans
      (Ideal.le_comap_pow (smoothCoordinateJetLift f r k hk) (k + 1))) hx
  rw [pow_ker_augmentedJetEvaluation_eq_bot] at hx'
  exact hx'

/-- The descended reverse map from the smooth jet to the polynomial jet. -/
noncomputable def smoothCoordinateJetSection
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    augmentedJet f k →ₐ[K]
      augmentedJet (polynomialOriginAugmentation (K := K) r) k :=
  Ideal.Quotient.liftₐ _ (smoothCoordinateJetLift f r k hk)
    (smoothCoordinateJetLift_pow_eq_zero f r k hk)

@[simp]
theorem smoothCoordinateJetSection_mk
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] (x : A) :
    smoothCoordinateJetSection f r k hk (Ideal.Quotient.mk _ x) =
      smoothCoordinateJetLift f r k hk x :=
  rfl

/-- The coordinate map followed by its descended section is the identity
on the smooth jet. -/
theorem comp_smoothCoordinateJetSection
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    (smoothCoordinateJetMap f r k).comp
        (smoothCoordinateJetSection f r k hk) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro x
  change smoothCoordinateJetMap f r k
      (smoothCoordinateJetLift f r k hk x) = Ideal.Quotient.mk _ x
  rw [← AlgHom.comp_apply, comp_smoothCoordinateJetLift]
  rfl

/-- The descended section respects augmentations. -/
theorem comp_smoothCoordinateJetSection_evaluation
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    (augmentedJetEvaluation
      (polynomialOriginAugmentation (K := K) r) k).comp
        (smoothCoordinateJetSection f r k hk) =
      augmentedJetEvaluation f k := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro x
  change augmentedJetEvaluation (polynomialOriginAugmentation r) k
      (smoothCoordinateJetLift f r k hk x) = f x
  rw [← AlgHom.comp_apply, comp_smoothCoordinateJetLift_evaluation]

/-- The reverse map is onto.  Surjectivity is propagated from first order
through the nilpotent augmentation filtration. -/
theorem smoothCoordinateJetSection_surjective
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    Function.Surjective (smoothCoordinateJetSection f r k hk) := by
  let e := polynomialOriginAugmentation (K := K) r
  let eA := augmentedJetEvaluation f k
  let eP := augmentedJetEvaluation e k
  let φ := smoothCoordinateJetMap f r k
  let ψ := smoothCoordinateJetSection f r k hk
  apply TranslatedDepthSeven.AlgHom.surjective_of_augmented_firstOrder_of_pow_ker_eq_bot
      ψ eA eP (comp_smoothCoordinateJetSection_evaluation f r k hk)
      k (pow_ker_augmentedJetEvaluation_eq_bot e k)
  intro x hx
  have hy : φ x ∈ RingHom.ker eA.toRingHom := by
    change eA (φ x) = 0
    rw [← AlgHom.comp_apply,
      comp_smoothCoordinateJetMap_evaluation]
    exact hx
  refine ⟨φ x, hy, ?_⟩
  apply ker_smoothCoordinateJetMap_le_square f r k hk
  change φ (x - ψ (φ x)) = 0
  rw [map_sub, ← AlgHom.comp_apply, comp_smoothCoordinateJetSection]
  simp

/-- Every positive-order jet at a standard-smooth rational point is
algebraically isomorphic to the corresponding truncated polynomial ring. -/
theorem smoothCoordinateJetMap_bijective
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    Function.Bijective (smoothCoordinateJetMap f r k) := by
  refine ⟨?_, smoothCoordinateJetMap_surjective f r k⟩
  intro x y hxy
  obtain ⟨x', rfl⟩ := smoothCoordinateJetSection_surjective f r k hk x
  obtain ⟨y', rfl⟩ := smoothCoordinateJetSection_surjective f r k hk y
  have hx' : smoothCoordinateJetMap f r k
      (smoothCoordinateJetSection f r k hk x') = x' :=
    AlgHom.congr_fun (comp_smoothCoordinateJetSection f r k hk) x'
  have hy' : smoothCoordinateJetMap f r k
      (smoothCoordinateJetSection f r k hk y') = y' :=
    AlgHom.congr_fun (comp_smoothCoordinateJetSection f r k hk) y'
  apply congrArg (smoothCoordinateJetSection f r k hk)
  exact hx'.symm.trans (hxy.trans hy')

/-- The explicit algebra equivalence between positive-order smooth and
polynomial jets. -/
noncomputable def smoothCoordinateJetAlgEquiv
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ) (hk : 1 ≤ k)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    augmentedJet (polynomialOriginAugmentation (K := K) r) k ≃ₐ[K]
      augmentedJet f k :=
  AlgEquiv.ofBijective (smoothCoordinateJetMap f r k)
    (smoothCoordinateJetMap_bijective f r k hk)

/-! ## The exact binomial jet formula -/

/-- The zeroth jet of any rational augmentation is the residue field. -/
noncomputable def augmentedJetZeroAlgEquiv
    {B : Type v} [CommRing B] [Algebra K B] (f : B →ₐ[K] K) :
    augmentedJet f 0 ≃ₐ[K] K := by
  change (B ⧸ RingHom.ker f.toRingHom ^ (0 + 1)) ≃ₐ[K] K
  rw [pow_one]
  exact Ideal.quotientKerAlgEquivOfSurjective fun x ↦
    ⟨algebraMap K B x, by simp⟩

/-- Every truncated polynomial algebra used above is finite-dimensional. -/
theorem polynomialOriginJet_moduleFinite (r k : ℕ) :
    Module.Finite K
      (augmentedJet (polynomialOriginAugmentation (K := K) r) k) := by
  let E := originPowerQuotientLinearEquivRestrictTotalDegree K r k
  letI : Module.Finite K
      (MvPolynomial.restrictTotalDegree (Fin r) K k) := inferInstance
  change Module.Finite K
    (MvPolynomial (Fin r) K ⧸
      RingHom.ker
        (MvPolynomial.constantCoeff : MvPolynomial (Fin r) K →+* K) ^ (k + 1))
  exact Module.Finite.equiv E.symm

/-- Every jet of a rational standard-smooth point is finite-dimensional. -/
theorem augmentedJet_moduleFinite_of_isStandardSmoothOfRelativeDimension
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    Module.Finite K (augmentedJet f k) := by
  cases k with
  | zero =>
      exact Module.Finite.equiv (augmentedJetZeroAlgEquiv f).symm.toLinearEquiv
  | succ k =>
      letI : Module.Finite K
          (augmentedJet (polynomialOriginAugmentation (K := K) r) (k + 1)) :=
        polynomialOriginJet_moduleFinite r (k + 1)
      exact Module.Finite.equiv
        (smoothCoordinateJetAlgEquiv f r (k + 1) (by omega)).toLinearEquiv

/-- Exact binomial length of every finite jet at a rational
standard-smooth point. -/
theorem finrank_augmentedJet_eq_choose_of_isStandardSmoothOfRelativeDimension
    {A : Type v} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r k : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    Module.finrank K (augmentedJet f k) = (k + r).choose r := by
  cases k with
  | zero =>
      rw [(augmentedJetZeroAlgEquiv f).toLinearEquiv.finrank_eq]
      simp
  | succ k =>
      let E := smoothCoordinateJetAlgEquiv f r (k + 1) (by omega)
      rw [← E.toLinearEquiv.finrank_eq]
      change Module.finrank K
        (MvPolynomial (Fin r) K ⧸
          RingHom.ker
            (MvPolynomial.constantCoeff :
              MvPolynomial (Fin r) K →+* K) ^ ((k + 1) + 1)) =
        ((k + 1) + r).choose r
      exact finrank_originPowerQuotient_eq_choose K r (k + 1)

/-! ## Application to the published multiplicity predicate -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 500000 in
/-- A standard-smooth rational point has Hilbert--Samuel multiplicity one
in the literal sense of `Published.HasHilbertSamuelMultiplicityAt`. -/
theorem hasHilbertSamuelMultiplicityAt_one_of_isStandardSmooth
    {N p : ℕ} (hp : p.Prime) [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin (N + 1)) (ZMod p)))
    (P : Fin (N + 1) → ZMod p) (r : ℕ)
    (hP : Published.IsPointOnSpecialFiber
      (Published.standardAffineChartIdeal J)
      (Published.standardAffineChartPoint P))
    [Algebra.IsStandardSmoothOfRelativeDimension r (ZMod p)
      (MvPolynomial (Fin N) (ZMod p) ⧸
        Published.standardAffineChartIdeal J)] :
    Published.HasHilbertSamuelMultiplicityAt hp J P r 1 := by
  let A := MvPolynomial (Fin N) (ZMod p) ⧸
    Published.standardAffineChartIdeal J
  let f : A →ₐ[ZMod p] ZMod p :=
    specialFiberQuotientEvaluationAlgHom
      (Published.standardAffineChartIdeal J)
      (Published.standardAffineChartPoint P) hP
  apply hasHilbertSamuelMultiplicityAt_one_of_finrank_specialFiberJetSpace_eq_choose
    hp J P r hP
  · intro k
    let E := specialFiberPointPowerQuotientAlgEquivJetSpace
      (Published.standardAffineChartIdeal J)
      (Published.standardAffineChartPoint P) hP k
    letI : Module.Finite (ZMod p)
        ((MvPolynomial (Fin N) (ZMod p) ⧸
          Published.standardAffineChartIdeal J) ⧸
            Published.specialFiberPointIdeal
              (Published.standardAffineChartIdeal J)
              (Published.standardAffineChartPoint P) hP ^ (k + 1)) := by
      change Module.Finite (ZMod p) (augmentedJet f k)
      exact augmentedJet_moduleFinite_of_isStandardSmoothOfRelativeDimension f r k
    exact Module.Finite.equiv E.toLinearEquiv
  · intro k
    let E := specialFiberPointPowerQuotientAlgEquivJetSpace
      (Published.standardAffineChartIdeal J)
      (Published.standardAffineChartPoint P) hP k
    rw [← E.toLinearEquiv.finrank_eq]
    exact finrank_augmentedJet_eq_choose_of_isStandardSmoothOfRelativeDimension
      f r k

end

end TranslatedDepthSeven
