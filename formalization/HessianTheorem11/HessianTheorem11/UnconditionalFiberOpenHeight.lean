import HessianTheorem11.UnconditionalFiberHeight
import HessianTheorem11.AffineOpenSets

/-! Heights at a point of an open affine subset are bounded by its actual
vanishing-ideal dimension. This is a direct prime-chain and Nullstellensatz
argument, with no fiber, smoothness, or generic-rank input. -/
noncomputable section
namespace HessianTheorem11.UnconditionalFiberOpenHeight
open MvPolynomial Ideal

/-- Restricting to an open neighborhood of a point does not remove any
prime chain below that point. The actual open set need not be irreducible. -/
theorem point_height_le_open_dimension {σ : Type} [Fintype σ]
    {A : Type*} [CommRing A]
    (q : MvPolynomial σ GeometricField →+* A) (hq : Function.Surjective q)
    (m : Ideal A) [m.IsPrime] (x : σ → GeometricField)
    (hm : m.comap q = vanishingIdeal GeometricField {x})
    (O : Set (σ → GeometricField))
    (hO : RelativelyOpenSet (zeroLocus GeometricField (RingHom.ker q)) O)
    (hx : x ∈ O) : (m.height : Dimension) ≤ affineDimension O := by
  obtain ⟨C, hC, he⟩ := hO
  have hxC : x ∉ C := (he ▸ hx).2
  obtain ⟨g, hg, hgx⟩ : ∃ g ∈ vanishingIdeal GeometricField C, eval x g ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hxC (hC ▸ hn)
  have hcontain (P : PrimeSpectrum A) (hP : P.asIdeal ≤ m) :
      vanishingIdeal GeometricField O ≤ P.asIdeal.comap q := by
    intro k hk
    have hprod : g*k ∈ (RingHom.ker q).radical := by
      rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (k := GeometricField) (K := GeometricField) (RingHom.ker q)]
      intro z hz
      by_cases hzC : z ∈ C
      · change eval z (g*k) = 0
        rw [map_mul, show eval z g = 0 from hg z hzC, zero_mul]
      · have hzO : z ∈ O := by rw [he]; exact ⟨hz, hzC⟩
        change eval z (g*k) = 0
        rw [map_mul, show eval z k = 0 from hk z hzO, mul_zero]
    have hker : RingHom.ker q ≤ P.asIdeal.comap q := by
      intro a ha
      change q a ∈ P.asIdeal
      rw [show q a = 0 from ha]
      exact P.asIdeal.zero_mem
    have hprodP : g*k ∈ P.asIdeal.comap q := by
      have h := Ideal.radical_mono hker hprod
      simpa only [Ideal.IsPrime.radical] using h
    apply (Ideal.IsPrime.mem_or_mem inferInstance hprodP).resolve_left
    intro hgP
    have hgm : g ∈ m.comap q := hP hgP
    rw [hm] at hgm
    exact hgx (hgm x (Set.mem_singleton x))
  rw [Ideal.height_eq_primeHeight, Ideal.primeHeight, Order.height_eq_krullDim_Iic]
  unfold affineDimension
  rw [ringKrullDim_quotient]
  let f : Set.Iic (⟨m, inferInstance⟩ : PrimeSpectrum A) →
      PrimeSpectrum.zeroLocus (R := MvPolynomial σ GeometricField)
        (vanishingIdeal GeometricField O) :=
    fun P => ⟨q.specComap P.val, hcontain P.val P.property⟩
  apply Order.krullDim_le_of_strictMono f
  intro P Q hPQ
  exact (RingHom.strictMono_specComap_of_surjective hq) hPQ

end HessianTheorem11.UnconditionalFiberOpenHeight
