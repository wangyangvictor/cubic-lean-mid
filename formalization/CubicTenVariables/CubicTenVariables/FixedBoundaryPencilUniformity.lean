import CubicTenVariables.FixedLeadingFormGoodReduction
import CubicTenVariables.CharacteristicZeroCertificateUniformity
import CubicTenVariables.FixedLeadingFormIntegralShear

/-!
# Uniform pencil certificates from one fixed boundary equation

For the pencil `F(T*x₂,x₀,x₁,x₂)`, the parameter-zero member is exactly
the boundary equation of `F`. If that boundary is a nonzero scalar multiple
of one fixed geometrically integral integral form, every relevant
characteristic-zero coefficient stratum has the same good anchor. The
proved Noetherian stratification theorem then bounds the degree of the
pencil certificate before every coefficient specialization. No Bertini
or degree-bound input is added.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option maxRecDepth 4000
noncomputable section

namespace CubicTenVariables.FixedBoundaryPencilUniformity

open MvPolynomial TranslatedDepthSeven
open HessianTheorem11.PolynomialRestriction
open FixedLeadingFormIntegralShear FixedLeadingFormGoodReduction
open CharacteristicZeroCertificateUniformity
open scoped Matrix

/-- The literal plane `x₀ = t*x₃` in projective three-space. -/
def pencilFrame {R : Type*} [CommRing R] (t : R) : Matrix (Fin 4) (Fin 3) R :=
  graphFrame (fun j => if j = 2 then t else 0)

theorem map_pencilFrame {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (t : R) : (pencilFrame t).map ρ = pencilFrame (ρ t) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · by_cases hj : j = 2 <;> simp [pencilFrame, graphFrame, Matrix.map_apply, hj]
  · by_cases hij : i = j <;>
      simp [pencilFrame, graphFrame, Matrix.map_apply, hij]

/-- The actual homogeneous plane equation with one polynomial parameter. -/
def pencilPolynomial {R : Type*} [CommRing R]
    (F : MvPolynomial (Fin 4) R) :
    MvPolynomial (Fin 3) (MvPolynomial (Fin 1) R) :=
  restrict (pencilFrame (X 0)) (map C F)

theorem pencilPolynomial_isHomogeneous {R : Type*} [CommRing R] {d : ℕ}
    (F : MvPolynomial (Fin 4) R) (hF : F.IsHomogeneous d) :
    (pencilPolynomial F).IsHomogeneous d :=
  homogeneous_restrict _ _ (hF.map _)

theorem specialize_pencilPolynomial {R K : Type*} [CommRing R] [CommRing K]
    (ρ : R →+* K) (t : Fin 1 → K) (F : MvPolynomial (Fin 4) R) :
    map (eval₂Hom ρ t) (pencilPolynomial F) =
      restrict (pencilFrame (t 0)) (map ρ F) := by
  have hc : (eval₂Hom ρ t).comp (C : R →+* MvPolynomial (Fin 1) R) = ρ := by
    ext r
    simp
  rw [pencilPolynomial, map_restrict, map_map, hc, map_pencilFrame]
  simp only [eval₂Hom_X']

/-- A fixed boundary identity is preserved by every coefficient map. -/
theorem boundary_identity_map {R K : Type*} [CommRing R] [CommRing K]
    (ρ : R →+* K) (F : MvPolynomial (Fin 4) R)
    (c : R) (k : MvPolynomial (Fin 3) ℤ)
    (hboundary : restrict (pencilFrame (0 : R)) F =
      C c * map (Int.castRingHom R) k) :
    restrict (pencilFrame (0 : K)) (map ρ F) =
      C (ρ c) * map (Int.castRingHom K) k := by
  have h := congrArg (map ρ) hboundary
  rw [map_restrict, map_pencilFrame, map_zero, map_mul, map_C, map_map] at h
  rwa [RingHom.ext_int (ρ.comp (Int.castRingHom R)) (Int.castRingHom K)] at h

/-- One exceptional integer and one detector degree work for all fields
and all specializations of the displayed Noetherian coefficient family.
The detector itself may depend on that specialization. -/
theorem exists_uniform_pencil_certificate
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {d : ℕ} (hd : 1 ≤ d)
    (k : MvPolynomial (Fin 3) ℤ) (hk : k.IsHomogeneous d)
    (hirr : Published.IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    (F : MvPolynomial (Fin 4) R) (hF : F.IsHomogeneous d) (c : R)
    (hboundary : restrict (pencilFrame (0 : R)) F =
      C c * map (Int.castRingHom R) k) :
    ∃ N : ℕ, 0 < N ∧ ∃ D : ℕ,
      ∀ (K : Type) [Field K] (ρ : R →+* K),
        (N : K) ≠ 0 → ρ c ≠ 0 →
        ∃ Δ : MvPolynomial (Fin 1) K, Δ ≠ 0 ∧ Δ.totalDegree ≤ D ∧
          ∀ t : Fin 1 → K, eval t Δ ≠ 0 →
            (restrict (pencilFrame (t 0)) (map ρ F)).totalDegree = d ∧
            IsDomain (MvPolynomial (Fin 3) (AlgebraicClosure K) ⧸
              Ideal.span {map (algebraMap K (AlgebraicClosure K))
                (restrict (pencilFrame (t 0)) (map ρ F))}) := by
  classical
  obtain ⟨Nk, hNk, hkred⟩ := exists_fixed_irreducible_reduction_certificate
    integralityOpen hd k hk hirr
  let Eligible : ∀ (K : Type) [Field K], (R →+* K) → Prop :=
    fun K _ ρ => ρ c ≠ 0
  let Good : ∀ (K : Type) [Field K], (R →+* K) → (Fin 1 → K) → Prop :=
    fun K _ ρ t =>
      (restrict (pencilFrame (t 0)) (map ρ F)).totalDegree = d ∧
        IsDomain (MvPolynomial (Fin 3) (AlgebraicClosure K) ⧸
          Ideal.span {map (algebraMap K (AlgebraicClosure K))
            (restrict (pencilFrame (t 0)) (map ρ F))})
  apply exists_uniform_degree_away_from_integer Eligible Good
  intro P hP hzero
  by_cases hcP : c ∈ P
  · refine ⟨1, hP.one_notMem, 0, ?_⟩
    intro K _ ρ hPρ _hs he
    exact (he (RingHom.mem_ker.mp (hPρ hcP))).elim
  letI : P.IsPrime := hP
  let B := R ⧸ P
  let q : R →+* B := Ideal.Quotient.mk P
  letI : CharZero B := charZero_of_inj_zero (fun a ha => by
    by_contra hne
    have hm : (a : R) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp (by
      simpa only [map_natCast] using ha)
    exact hzero a (Nat.pos_of_ne_zero hne) hm)
  let L := FractionRing B
  let Ω := AlgebraicClosure L
  let κ : B →+* Ω := (algebraMap L Ω).comp (algebraMap B L)
  have hκ : Function.Injective κ :=
    (algebraMap L Ω).injective.comp (IsFractionRing.injective B L)
  have hcB : q c ≠ 0 := fun hz => hcP (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hcΩ : κ (q c) ≠ 0 := fun hz => hcB (hκ (by simpa using hz))
  have hNkL : (Nk : L) ≠ 0 := by exact_mod_cast hNk
  have hkirr : Irreducible (map (Int.castRingHom Ω) k) := by
    have h := (hkred L hNkL).2
    rw [map_map] at h
    rwa [RingHom.ext_int ((algebraMap L Ω).comp (Int.castRingHom L))
      (Int.castRingHom Ω)] at h
  let Fbar := map q F
  let ψ : MvPolynomial (Fin 1) B →+* Ω := eval₂Hom κ (fun _ => 0)
  have hanchor : map ψ (pencilPolynomial Fbar) =
      C (κ (q c)) * map (Int.castRingHom Ω) k := by
    rw [specialize_pencilPolynomial]
    dsimp only [Fbar]
    rw [map_map]
    exact boundary_identity_map (κ.comp q) F c k hboundary
  have hanchorIrr : Irreducible (map ψ (pencilPolynomial Fbar)) := by
    rw [hanchor]
    exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr hcΩ).map C)).2 hkirr
  have hanchorDomain : IsDomain (MvPolynomial (Fin 3) Ω ⧸
      Ideal.span {map ψ (pencilPolynomial Fbar)}) := by
    apply (Ideal.Quotient.isDomain_iff_prime _).mpr
    exact (Ideal.span_singleton_prime hanchorIrr.ne_zero).mpr hanchorIrr.prime
  obtain ⟨s, hs, hopen⟩ := integralityOpen (MvPolynomial (Fin 1) B) Ω 3 d hd
    ψ (pencilPolynomial Fbar) (pencilPolynomial_isHomogeneous _ (hF.map q))
    hanchorIrr.ne_zero hanchorDomain
  have hs0 : κ (constantCoeff s) ≠ 0 := by
    simpa only [ψ, eval₂Hom_zero'_apply] using hs
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (constantCoeff s)
  refine ⟨r, ?_, s.totalDegree, ?_⟩
  · intro hrP
    apply hs0
    rw [← hr, Ideal.Quotient.eq_zero_iff_mem.mpr hrP, map_zero]
  · intro K _ ρ hPρ hrρ _he
    let τ : B →+* K := Ideal.Quotient.lift P ρ
      (fun _ hx => RingHom.mem_ker.mp (hPρ hx))
    have hcomp : τ.comp q = ρ := Ideal.Quotient.lift_comp_mk P ρ _
    have hsK : τ (constantCoeff s) ≠ 0 := by
      rw [← hr]
      exact hrρ
    refine ⟨map τ s, ?_, Finset.sup_mono (support_map_subset τ s), ?_⟩
    · intro hz
      apply hsK
      rw [← constantCoeff_map, hz, map_zero]
    · intro t ht
      have ht' : eval₂Hom τ t s ≠ 0 := by
        simpa only [eval_map] using ht
      have hh := hopen K (eval₂Hom τ t) ht'
      have hmapF : map τ Fbar = map ρ F := by
        dsimp only [Fbar]
        rw [map_map, hcomp]
      have hspecial : map (eval₂Hom τ t) (pencilPolynomial Fbar) =
          restrict (pencilFrame (t 0)) (map ρ F) := by
        rw [specialize_pencilPolynomial, hmapF]
      rw [hspecial] at hh
      exact hh

end CubicTenVariables.FixedBoundaryPencilUniformity
