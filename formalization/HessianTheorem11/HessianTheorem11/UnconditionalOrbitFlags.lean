import HessianTheorem11.UnconditionalOrbitGlobal
import HessianTheorem11.UnconditionalOrbitMaximumTransport
import HessianTheorem11.UnconditionalWeightMixedUnique
import HessianTheorem11.UnconditionalSpecialLinearFrame

/-! A common splitting and strict convexity prove uniqueness of the
actual integer-indexed weighted flag for equal-norm relative maximizers.
The single common matrix is normalized to determinant one once, for all
weights, so every comparison remains inside the special-linear action. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitGlobal
open MvPolynomial PolynomialRestriction PolynomialWeightTransport RationalDescent ReducedRelative
  UnconditionalOrbitIdeal UnconditionalOrbitWeights UnconditionalWeightOptimization
  UnconditionalFlags UnconditionalSpecialLinearFrame
variable {K : Type*} [Field K] [Infinite K] {n d : ℕ}

theorem slMaximizer_fixed_support (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (f : WeightFrame K n) (hf : SLMaximizingFrame d F S f) (N : ℕ)
    (hgen : Ideal.span (boundedIdeal (finiteTarget (d := d) S) N :
      Set (MvPolynomial (DegreeIndex n d) K)) = vanishingIdeal K (finiteTarget (d := d) S)) :
    (∀ a ∈ activeCharacters (d := d) (restrict f.matrix F) S N,
      0 < UnconditionalWeightMixed.integralCharacter a f.weight) ∧
    ∀ v : Fin n → ℤ, (∑ i, v i) = 0 →
      (∀ a ∈ weakCharacters (restrict f.matrix F),
        0 ≤ UnconditionalWeightMixed.integralCharacter a v) →
      UnconditionalWeightMixed.finiteSpeed
        (activeCharacters (d := d) (restrict f.matrix F) S N) v ≤
      UnconditionalWeightMixed.finiteSpeed
        (activeCharacters (d := d) (restrict f.matrix F) S N) f.weight := by
  constructor
  · intro a ha
    have hh := (le_relativeOrder_iff_activeCharacters hn (restrict f.matrix F)
      (homogeneous_restrict f.matrix F hF) S hclosed hS hhom
      (restrict_not_mem_target F S hS hnot f.matrix hf.det_one) f.weight f.sum_zero
      hf.admissible N (relativeOrder d F S f) hgen).mp
      (le_of_eq (relativeOrder_coordinate F hF S hclosed hS hhom hnot f hf.det_one)) a ha
    exact lt_of_lt_of_le (mul_pos (by exact_mod_cast hn)
      (by exact_mod_cast hf.positive_order)) hh
  · intro v hv hvW
    let g : WeightFrame K n := ⟨f.matrix,f.injective,v,hv⟩
    have hg : HasNonnegativeWeights (restrict g.matrix F) g.weight :=
      (hasNonnegativeWeights_iff_weakCharacters _ _).mpr hvW
    have hh := hf.maximal g hf.det_one hg
    rw [relativeSpeed_eq_finiteSpeed_div hn F hF S hclosed hS hhom hnot g hf.det_one hg N hgen,
      relativeSpeed_eq_finiteSpeed_div hn F hF S hclosed hS hhom hnot f hf.det_one
        hf.admissible N hgen] at hh
    exact (div_le_div_iff_of_pos_right (by exact_mod_cast hn : (0 : ℝ) < n)).mp hh

/-- Equal-norm global relative maximizers have exactly the same flag at
every integer level. No primitive convention or flag-uniqueness input is
used. In particular Galois-conjugate maximizers satisfy this conclusion. -/
theorem maximizing_flag_eq_of_norm_eq (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (f g : WeightFrame K n) (hf : SLMaximizingFrame d F S f)
    (hg : SLMaximizingFrame d F S g)
    (hnorm : ‖realWeight f.weight‖ = ‖realWeight g.weight‖) : f.flag = g.flag := by
  classical
  obtain ⟨b,w,u,hw,hu,hws,hus⟩ :=
    exists_common_weighted_basis (frameBasis f) (frameBasis g) f.weight g.weight
  have hbdet : (basisMatrix b).det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.mulVec_injective_iff_isUnit.mp (basisMatrix_injective b)))
  let C := normalizeMatrix hn (basisMatrix b)
  have hCdet : C.det = 1 := normalizeMatrix_det hn (basisMatrix b) hbdet
  have hCinj : Function.Injective C.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (hCdet ▸ isUnit_one))
  have hwflag : weightFlag C w = f.flag := by
    rw [frameBasis_flag] at hw
    exact (normalizeMatrix_flag hn (basisMatrix b) hbdet w).trans hw
  have huflag : weightFlag C u = g.flag := by
    rw [frameBasis_flag] at hu
    exact (normalizeMatrix_flag hn (basisMatrix b) hbdet u).trans hu
  have hwsum : ∑ i, w i = 0 := by
    have h := hws (fun z => (z : ℝ))
    have hfzero : (∑ i, (f.weight i : ℝ)) = 0 := by exact_mod_cast f.sum_zero
    rw [hfzero] at h
    exact_mod_cast h
  have husum : ∑ i, u i = 0 := by
    have h := hus (fun z => (z : ℝ))
    have hgzero : (∑ i, (g.weight i : ℝ)) = 0 := by exact_mod_cast g.sum_zero
    rw [hgzero] at h
    exact_mod_cast h
  have hwnorm := realWeight_norm_of_square_sum w f.weight (hws (fun z => (z : ℝ)^2))
  have hunorm := realWeight_norm_of_square_sum u g.weight (hus (fun z => (z : ℝ)^2))
  let fw : WeightFrame K n := ⟨C,hCinj,w,hwsum⟩
  let gu : WeightFrame K n := ⟨C,hCinj,u,husum⟩
  have hfw : SLMaximizingFrame d F S fw := slMaximizingFrame_of_same_flag
    F hF S hclosed hS hhom hnot f fw hf hCdet hwflag.symm hwnorm.symm
  have hgu : SLMaximizingFrame d F S gu := slMaximizingFrame_of_same_flag
    F hF S hclosed hS hhom hnot g gu hg hCdet huflag.symm hunorm.symm
  obtain ⟨N,hgen⟩ := exists_boundedIdeal_generates (finiteTarget (d := d) S)
  obtain ⟨hwpos,hwmax⟩ := slMaximizer_fixed_support hn F hF S hclosed hS hhom hnot fw hfw N hgen
  obtain ⟨hupos,humax⟩ := slMaximizer_fixed_support hn F hF S hclosed hS hhom hnot gu hgu N hgen
  have hT := activeCharacters_nonempty (restrict C F) (homogeneous_restrict C F hF)
    S hclosed hhom (restrict_not_mem_target F S hS hnot C hCdet) N hgen
  have he : w = u := UnconditionalWeightMixed.same_norm_integer_maximizers_equal
    hT w u hwsum husum
    ((hasNonnegativeWeights_iff_weakCharacters _ _).mp hfw.admissible)
    ((hasNonnegativeWeights_iff_weakCharacters _ _).mp hgu.admissible)
    hwpos hupos hwmax humax (hwnorm.trans (hnorm.trans hunorm.symm))
  rw [← hwflag,← huflag,he]

end HessianTheorem11.UnconditionalOrbitGlobal
