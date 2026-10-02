import TranslatedDepthSeven.SmoothHilbertSamuelMultiplicityOne
import TranslatedDepthSeven.TruncatedPolynomialJets

/-!
# Standard-smooth rational points and polynomial jets

At a rational point of a standard-smooth algebra, choose representatives of
a basis of `m / m²`.  They define a map from affine space to the algebra.
This file carries out the resulting comparison of finite infinitesimal
neighbourhoods directly.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v

variable {K : Type u} {A : Type v}
variable [Field K] [CommRing A] [Algebra K A]

/-- The constant-term augmentation of a polynomial ring. -/
noncomputable def polynomialOriginAugmentation (r : ℕ) :
    MvPolynomial (Fin r) K →ₐ[K] K where
  toRingHom := MvPolynomial.constantCoeff
  commutes' c := MvPolynomial.constantCoeff_C (Fin r) c

/-- A basis of the cotangent space at a rational standard-smooth point. -/
noncomputable def smoothCotangentBasis
    (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    Module.Basis (Fin r) K (RingHom.ker f.toRingHom).Cotangent := by
  letI : Module.Finite K (RingHom.ker f.toRingHom).Cotangent :=
    cotangent_moduleFinite_of_isStandardSmoothOfRelativeDimension f r
  exact Module.finBasisOfFinrankEq K _
    (finrank_cotangent_of_isStandardSmoothOfRelativeDimension f r)

/-- A chosen representative in the augmentation ideal of every cotangent
class. -/
noncomputable def cotangentRepresentative (f : A →ₐ[K] K) :
    (RingHom.ker f.toRingHom).Cotangent → RingHom.ker f.toRingHom :=
  Function.surjInv (RingHom.ker f.toRingHom).toCotangent_surjective

@[simp]
theorem toCotangent_cotangentRepresentative (f : A →ₐ[K] K)
    (x : (RingHom.ker f.toRingHom).Cotangent) :
    (RingHom.ker f.toRingHom).toCotangent (cotangentRepresentative f x) = x :=
  Function.surjInv_eq
    (RingHom.ker f.toRingHom).toCotangent_surjective x

/-- Chosen affine coordinates whose first-order classes are a cotangent
basis. -/
noncomputable def smoothCoordinate (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] : Fin r → A :=
  fun i ↦ cotangentRepresentative f (smoothCotangentBasis f r i)

/-- The polynomial map determined by the chosen smooth coordinates. -/
noncomputable def smoothCoordinateMap (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    MvPolynomial (Fin r) K →ₐ[K] A :=
  MvPolynomial.aeval (smoothCoordinate f r)

/-- The chosen coordinate map respects the two augmentations. -/
theorem comp_smoothCoordinateMap_eq_polynomialOriginAugmentation
    (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    f.comp (smoothCoordinateMap f r) = polynomialOriginAugmentation r := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, smoothCoordinateMap, MvPolynomial.aeval_X,
    polynomialOriginAugmentation, smoothCoordinate]
  change f (cotangentRepresentative f (smoothCotangentBasis f r i)) =
    MvPolynomial.constantCoeff (MvPolynomial.X i)
  rw [MvPolynomial.constantCoeff_X]
  exact (cotangentRepresentative f (smoothCotangentBasis f r i)).prop

/-- Every element of the augmentation ideal agrees modulo its square with
a linear polynomial in the chosen smooth coordinates. -/
theorem smoothCoordinateMap_firstOrder_approximation
    (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A]
    (x : A) (hx : x ∈ RingHom.ker f.toRingHom) :
    ∃ p : MvPolynomial (Fin r) K,
      p ∈ RingHom.ker (polynomialOriginAugmentation (K := K) r).toRingHom ∧
      x - smoothCoordinateMap f r p ∈ RingHom.ker f.toRingHom ^ 2 := by
  let m : Ideal A := RingHom.ker f.toRingHom
  let b := smoothCotangentBasis f r
  let v : m.Cotangent := m.toCotangent ⟨x, hx⟩
  let p : MvPolynomial (Fin r) K :=
    ∑ i, MvPolynomial.C (b.repr v i) * MvPolynomial.X i
  refine ⟨p, ?_, ?_⟩
  · change MvPolynomial.constantCoeff p = 0
    simp [p]
  · have hpzero : MvPolynomial.constantCoeff p = 0 := by simp [p]
    have hpmem : smoothCoordinateMap f r p ∈ m := by
      change f (smoothCoordinateMap f r p) = 0
      rw [← AlgHom.comp_apply,
        comp_smoothCoordinateMap_eq_polynomialOriginAugmentation]
      exact hpzero
    have hsubtype :
        (⟨smoothCoordinateMap f r p, hpmem⟩ : m) =
          ∑ i, (b.repr v i) •
            cotangentRepresentative f (smoothCotangentBasis f r i) := by
      apply Subtype.ext
      simp [p, smoothCoordinateMap, smoothCoordinate, Algebra.smul_def, b]
    change x - smoothCoordinateMap f r p ∈ m ^ 2
    have heq : m.toCotangent ⟨x, hx⟩ =
        m.toCotangent ⟨smoothCoordinateMap f r p, hpmem⟩ := by
      rw [hsubtype, map_sum]
      change v = ∑ i, m.toCotangent
        ((b.repr v i) • cotangentRepresentative f (b i))
      simp_rw [m.toCotangent.map_smul_of_tower]
      have hrep (i : Fin r) :
          m.toCotangent (cotangentRepresentative f (b i)) = b i := by
        simpa [m, b] using
          toCotangent_cotangentRepresentative f (b i)
      simp_rw [hrep]
      exact (b.sum_repr v).symm
    simpa using m.toCotangent_eq.mp heq

end

end TranslatedDepthSeven
