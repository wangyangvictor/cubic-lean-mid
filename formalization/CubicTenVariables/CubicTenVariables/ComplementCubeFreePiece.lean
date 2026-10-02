import CubicTenVariables.ComplementPieceAverage
import CubicTenVariables.CubeFreeNonzeroAverage

/-! Canonical reindexing of the complete piece mean into actual cube-free
moduli. Each original modulus/frequency pair is counted exactly once. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementCubeFreePiece
open MvPolynomial HessianTheorem11 NumericalPrimeDepth
open SquarefullModulusDecomposition CubeFreeModulusDecomposition
open scoped BigOperators

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C : ℝ} {d₀ : ℕ} {h : CoarseBounds F C}

abbrev Sample := ℕ × (Fin 10 → ℤ)

/-- The literal pointwise restrictions on a cube-free modulus and vector. -/
structure InPiece (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1))
    (N : ℕ) (h : CoarseBounds F C) (i : Fin 5) (D : ℝ)
    (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ) (v₀ : Fin 10 → ℤ) (x : Sample) : Prop where
  window : x.1 ∈ CubeFreeNonzeroAverage.window D
  good_primes : x.1.Coprime N
  progression_coprime : m.Coprime x.1
  piece : (fun k => (x.2 k : ℚ)) ∈ ComplementFrequencyPieces.piece F f tables i
  box : ∀ k, |(x.2 k : ℝ)-u k| ≤ L
  progression : ∀ k, (m : ℤ) ∣ x.2 k-v₀ k
  open_cutoff : i.val=0 → 1+L/(m : ℝ) < (NumericalConductorRadical.R22 h (d x.1) (c x.1) x.2 : ℝ)

theorem exists_bound
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (i : Fin 5) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L → ∀ m : ℕ, 0 < m →
      ∀ (v₀ : Fin 10 → ℤ) (E : Finset Sample),
      (∀ x ∈ E, InPiece F f tables N h i D u L m v₀ x) →
      (∑ x ∈ E, ‖completeCubicSum F x.1 x.2‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((59 : ℝ)/6)*
          ((1+L/(m : ℝ))/D^((1 : ℝ)/3)+((1+L/(m : ℝ))/D^((1 : ℝ)/3))^9) := by
  classical
  obtain ⟨M,hM,hbound⟩ := ComplementPieceAverage.exists_bound hP hhom hAn hc i ε hε
  refine ⟨M,hM,?_⟩
  intro D hD u L hL m hm v₀ E hE
  let lift : Sample → ComplementAllocationSamples.Sample := fun x => ((d x.1,c x.1),x.2)
  have hcube (x : Sample) (hx : x ∈ E) : CubeFree x.1 :=
    ((CubeFreeNonzeroAverage.mem_window D x.1).mp (hE x hx).window).1
  have hinj : Set.InjOn lift (↑E : Set Sample) := by
    intro x hx y hy he
    apply Prod.ext
    · exact CubeFreeModulusDecomposition.parameters_injOn
        (Nat.pos_of_ne_zero (hcube x hx).1) (Nat.pos_of_ne_zero (hcube y hy).1)
        (congrArg Prod.fst he)
    · have hv : (lift x).2 = (lift y).2 := congrArg Prod.snd he
      exact hv
  have hdata : ∀ y ∈ E.image lift,
      ComplementPieceAverage.InPiece F f tables N h i D u L m v₀ y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    have hh := hE x hx
    have hq := hcube x hx
    have he := eq_d_mul_c_sq x.1 hq
    refine ⟨d_squarefree x.1,c_squarefree x.1 hq,coprime_d_c x.1 hq,?_,?_,?_,
      hh.piece,hh.box,hh.progression,hh.open_cutoff⟩
    · have hs := ((CubeFreeNonzeroAverage.mem_window D x.1).mp hh.window).2.2.le
      have he' : (x.1 : ℝ)=(d x.1 : ℝ)*(c x.1 : ℝ)^2 := by exact_mod_cast he
      simpa only [lift,he'] using hs
    · simpa only [lift,← he] using hh.good_primes
    · simpa only [lift,← he] using hh.progression_coprime
  have hs := hbound D hD u L hL m hm v₀ (E.image lift) hdata
  have he : (∑ y ∈ E.image lift, ‖completeCubicSum F (y.1.1*y.1.2^2) y.2‖) =
      ∑ x ∈ E, ‖completeCubicSum F x.1 x.2‖ := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro x hx
    change ‖completeCubicSum F (d x.1*(c x.1)^2) x.2‖ = _
    rw [← eq_d_mul_c_sq x.1 (hcube x hx)]
  rwa [he] at hs

end CubicTenVariables.ComplementCubeFreePiece
