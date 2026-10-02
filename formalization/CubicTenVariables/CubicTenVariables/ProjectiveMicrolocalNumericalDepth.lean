import CubicTenVariables.ProjectiveMicrolocalTraceBound

/-! The actual nonnegative integer depth of a geometric equation fiber.
The empty fiber has depth zero. Finiteness follows from the number of fiber
variables, so the ENat-toNat operation never discards an infinite dimension
in the applications below. The trace bounds use this computed depth and
retain the supplied GoodReduction certificate as an explicit hypothesis. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ProjectiveMicrolocalNumericalDepth

open MvPolynomial HessianTheorem11 ProjectiveMicrolocalData
open ProjectiveFourierIdentity

/-- Natural-valued truncation of a dimension. The proofs below require a
finite upper bound before identifying it with max(0,dimension). -/
def nonnegativeDepth (d : Dimension) : ℕ := (d.unbotD 0).toNat

theorem nonnegativeDepth_bot : nonnegativeDepth ⊥ = 0 := by
  simp [nonnegativeDepth]

theorem nonnegativeDepth_nat (n : ℕ) : nonnegativeDepth (n : Dimension) = n := by
  change (((n : ℕ∞) : WithBot ℕ∞).unbotD 0).toNat = n
  rw [WithBot.unbotD_coe]
  simp

/-- A finite upper bound rules out infinite dimension. -/
theorem nonnegativeDepth_le {d : Dimension} {n : ℕ} (hd : d ≤ (n : Dimension)) :
    nonnegativeDepth d ≤ n := by
  have hu : d.unbotD 0 ≤ (n : ℕ∞) :=
    (WithBot.unbotD_le_iff (by intro _; positivity)).mpr hd
  exact ENat.toNat_le_of_le_coe hu

/-- Exact max with zero, including the empty-fiber convention. -/
theorem coe_nonnegativeDepth_eq_max {d : Dimension} {n : ℕ}
    (hd : d ≤ (n : Dimension)) :
    (nonnegativeDepth d : Dimension) = max d 0 := by
  have hu : d.unbotD 0 ≤ (n : ℕ∞) :=
    (WithBot.unbotD_le_iff (by intro _; positivity)).mpr hd
  have hf : d.unbotD 0 ≠ ⊤ := ne_top_of_le_ne_top (by simp) hu
  have hc : (nonnegativeDepth d : ℕ∞) = d.unbotD 0 := ENat.coe_toNat hf
  change ((nonnegativeDepth d : ℕ∞) : Dimension) = max d 0
  rw [hc]
  cases d using WithBot.recBotCoe with
  | bot => simp
  | coe a =>
    rw [WithBot.unbotD_coe]
    symm
    apply max_eq_left
    change ((0 : ℕ∞) : WithBot ℕ∞) ≤ (a : WithBot ℕ∞)
    exact_mod_cast (show (0 : ℕ∞) ≤ a by positivity)

theorem dimension_le_nonnegativeDepth {d : Dimension} {n : ℕ}
    (hd : d ≤ (n : Dimension)) : d ≤ (nonnegativeDepth d : Dimension) := by
  rw [coe_nonnegativeDepth_eq_max hd]
  exact le_max_left _ _

/-- The depth is computed from the actual specialized equation quotient
over an algebraic closure, not supplied as an additional parameter. -/
def depth {m n : ℕ} {ι : Type*}
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (v : Fin m → K) : ℕ :=
  nonnegativeDepth (IntegralGeometricFiberDepth.geometricFiberDimension f K v)

theorem depth_le {m n : ℕ} {ι : Type*}
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (v : Fin m → K) : depth f K v ≤ n :=
  nonnegativeDepth_le (IntegralGeometricFiberDepth.geometricFiberDimension_le f K v)

theorem depth_eq_max {m n : ℕ} {ι : Type*}
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (v : Fin m → K) :
    (depth f K v : Dimension) =
      max (IntegralGeometricFiberDepth.geometricFiberDimension f K v) 0 :=
  coe_nonnegativeDepth_eq_max
    (IntegralGeometricFiberDepth.geometricFiberDimension_le f K v)

theorem geometricFiberDimension_le_depth {m n : ℕ} {ι : Type*}
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (v : Fin m → K) :
    IntegralGeometricFiberDepth.geometricFiberDimension f K v ≤ (depth f K v : Dimension) :=
  dimension_le_nonnegativeDepth
    (IntegralGeometricFiberDepth.geometricFiberDimension_le f K v)

/-- Every nonzero finite-field frequency, with its actual geometric depth. -/
theorem normalizedFourierSum_bound {n d t : ℕ} (hn : 3 ≤ n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial n n) (N B : ℕ)
    (h : GoodReduction F f N B) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ N)
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (v : Fin n → K) (hv : v ≠ 0) :
    ‖normalizedFourierSum ψ (map (Int.castRingHom K) F) v‖ ≤
      (1+2*(B : ℝ)) * (Fintype.card K : ℝ)^(((n : ℝ)-1+(depth f K v : ℝ))/2) :=
  ProjectiveMicrolocalTraceBound.normalizedFourierSum_bound hn F hF hd f N B h p hp
    K ψ hψ v hv (depth f K v) (geometricFiberDimension_le_depth f K v)

/-- Every nonzero reduced prime frequency, with the same actual depth. -/
theorem completeCubicSum_bound {n d t : ℕ} (hn : 3 ≤ n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial n n) (N B : ℕ)
    (h : GoodReduction F f N B) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ N)
    (v : Fin n → ℤ) (hv : (fun i => (v i : ZMod p)) ≠ 0) :
    ‖completeCubicSum F p v‖ ≤
      (1+2*(B : ℝ)) * (p : ℝ)^(((n : ℝ)+1+
        (depth f (ZMod p) (fun i => (v i : ZMod p)) : ℝ))/2) :=
  ProjectiveMicrolocalTraceBound.completeCubicSum_bound hn F hF hd f N B h p hp
    v hv _ (geometricFiberDimension_le_depth f (ZMod p) _)

end CubicTenVariables.ProjectiveMicrolocalNumericalDepth
