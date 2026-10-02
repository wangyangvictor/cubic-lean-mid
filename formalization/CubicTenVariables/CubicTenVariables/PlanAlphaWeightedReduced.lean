import CubicTenVariables.CubeFreeWeightedPointwiseReduced
import CubicTenVariables.CubeFreeWeightedResiduesReduced
import CubicTenVariables.PlanAlphaHolderNumerics

/-! Plan Alpha's single weighted cube-free estimate. Both alternatives in
the minimum and the Hölder term are retained. The finite sample set allows
arbitrary further restrictions on the moduli or pairs. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.PlanAlphaWeightedReduced
open MvPolynomial HessianTheorem11 NumericalPrimeDepth
open SquarefullModulusDecomposition CubeFreeModulusDecomposition
open ComplementCubeFreePiece (Sample)
open ConductorFixedFrequency (GoodFrequency)
open IntegerResidueClasses (residue)
open scoped BigOperators Classical

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C : ℝ} {d₀ : ℕ} {h : CoarseBounds F C}

/-- A uniform weighted bound on arbitrary finite subsets of the literal
cube-free summation domain. Weights and their periodic majorant depend
only on the frequency, and their masses are unnormalised sums. -/
theorem of_data
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ) [NeZero m],
      ∀ (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ)
        (P : (Fin 10 → ZMod m) → ℝ),
      (∀ v ∈ V, v ≠ 0 ∧ ∀ k, |(v k : ℝ)-u k| ≤ L) →
      (∀ v ∈ V, 0 ≤ w v) → (∀ b, 0 ≤ P b) →
      (∀ v ∈ V, w v ≤ P (residue m v)) →
      ∀ E : Finset Sample,
      (∀ x ∈ E, x.1 ∈ CubeFreeNonzeroAverage.window D ∧ x.1.Coprime (m*N) ∧ x.2 ∈ V) →
      (∑ x ∈ E, w x.2*‖completeCubicSum F x.1 x.2‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε *
          (min (D^((59 : ℝ)/6)*
            ((1+L/(m : ℝ))/D^((1 : ℝ)/3)+((1+L/(m : ℝ))/D^((1 : ℝ)/3))^9)*(∑ b, P b))
            (D^9*(∑ v ∈ V, w v)) +
           D^((13 : ℝ)/2)*(1+L/(m : ℝ))^((20 : ℝ)/3)*
             (∑ b, P b)^((2 : ℝ)/3)*(∑ v ∈ V, w v)^((1 : ℝ)/3)) := by
  obtain ⟨Mc,hMc,hcomp⟩ := CubeFreeWeightedResiduesReduced.exists_complement_bound
    integrality cubicWeil isolated pointcount hP hhom hAn hc ε hε
  obtain ⟨Mo,hMo,hcoarse⟩ := CubeFreeWeightedPointwiseReduced.exists_coarse_bound
    integrality cubicWeil isolated pointcount hP hhom hAn ε hε
  obtain ⟨Mp,hMp,hpositive⟩ := CubeFreeWeightedResiduesReduced.exists_positive_bound
    pointcount hP hhom hAn hc ε hε
  obtain ⟨Mi,hMi,hinverse⟩ := CubeFreeWeightedPointwiseReduced.exists_inverse_bound hhom hc ε hε
  let M := Mc+Mo+Mp+Mi
  have hMcM : Mc ≤ M := by dsimp [M]; linarith
  have hMoM : Mo ≤ M := by dsimp [M]; linarith
  have hMpM : Mp ≤ M := by dsimp [M]; linarith
  have hMiM : Mi ≤ M := by dsimp [M]; linarith
  have hM : 1 ≤ M := hMc.trans hMcM
  refine ⟨M,hM,?_⟩
  intro D hD u L hL m hm V w P hV hw hP0 hmajor E hE
  let T : ℝ := 1+L/(m : ℝ)
  let δ : ℝ := (D*(2+‖u‖+L+(m : ℝ)))^ε
  let U : ℝ := M*δ
  let X : ℝ := U*D^((13 : ℝ)/2)
  let P₁ : ℝ := ∑ b, P b
  let W₁ : ℝ := ∑ v ∈ V, w v
  let A : ℝ := D^((59 : ℝ)/6)*(T/D^((1 : ℝ)/3)+(T/D^((1 : ℝ)/3))^9)*P₁
  let R : ℝ := D^9*W₁
  let G : ℝ := D^((13 : ℝ)/2)*T^((20 : ℝ)/3)*P₁^((2 : ℝ)/3)*W₁^((1 : ℝ)/3)
  let good (x : Sample) : Prop := GoodFrequency F f tables x.2 ∧
    (NumericalConductorRadical.R22 h (d x.1) (c x.1) x.2 : ℝ) ≤ T
  let Egood := E.filter good
  let Ebad := E.filter (fun x => ¬good x)
  let Vgood := V.filter (GoodFrequency F f tables)
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hU0 : 0 ≤ U := mul_nonneg (zero_le_one.trans hM) hδ0
  have hX0 : 0 ≤ X := mul_nonneg hU0 (Real.rpow_nonneg hD0 _)
  have hP₁ : 0 ≤ P₁ := Finset.sum_nonneg fun b _ => hP0 b
  have hW₁ : 0 ≤ W₁ := Finset.sum_nonneg hw
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hR0 : 0 ≤ R := mul_nonneg (pow_nonneg hD0 _) hW₁
  have scale (a Z : ℝ) (ha : a ≤ M) (hZ : 0 ≤ Z) : a*δ*Z ≤ U*Z :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hδ0) hZ
  have hbad : ∀ x ∈ Ebad, CubeFreeWeightedResiduesReduced.InComplement F f tables N h D u L m x := by
    intro x hx
    obtain ⟨hx,hnot⟩ := Finset.mem_filter.mp hx
    obtain ⟨hq,hcop,hv⟩ := hE x hx
    have hcop' := Nat.coprime_mul_iff_right.mp hcop
    refine ⟨hq,hcop'.2,hcop'.1.symm,(hV x.2 hv).1,(hV x.2 hv).2,?_⟩
    rcases not_and_or.mp hnot with hn | hn
    · exact Or.inl hn
    · exact Or.inr (lt_of_not_ge hn)
  have hgood : ∀ x ∈ Egood, CubeFreeWeightedResiduesReduced.InPositive F f tables h D u L m x := by
    intro x hx
    obtain ⟨hx,hg⟩ := Finset.mem_filter.mp hx
    obtain ⟨hq,hcop,hv⟩ := hE x hx
    exact ⟨hq,(Nat.coprime_mul_iff_right.mp hcop).1.symm,hg.1,(hV x.2 hv).2,hg.2⟩
  have hEbad : Ebad ⊆ E := Finset.filter_subset _ _
  have hEgood : Egood ⊆ E := Finset.filter_subset _ _
  have hc_bound : (∑ x ∈ Ebad, w x.2*‖completeCubicSum F x.1 x.2‖) ≤ U*A := by
    have hb := hcomp D hD u L hL m Ebad w P hbad hP0
      (fun x hx => hmajor x.2 (hE x (hEbad hx)).2.2)
    calc
      _ ≤ Mc*δ*A := by convert hb using 1 <;> dsimp [δ,A,T,P₁] <;> ring
      _ ≤ _ := scale Mc A hMcM hA0
  have ho_bound : (∑ x ∈ Ebad, w x.2*‖completeCubicSum F x.1 x.2‖) ≤ U*R := by
    have hs := FiniteWeightedClassSum.sum_subset_product_le Ebad (CubeFreeNonzeroAverage.window D) V
      (fun q v => w v*‖completeCubicSum F q v‖)
      (fun x hx => Finset.mem_product.mpr ⟨(hE x (hEbad hx)).1,(hE x (hEbad hx)).2.2⟩)
      (fun q _ v hv => mul_nonneg (hw v hv) (norm_nonneg _))
    have hb := hcoarse D hD u L hL0 m V w hw (fun v hv => (hV v hv).2)
      (fun v hv => (hV v hv).1)
    calc
      _ ≤ Mo*δ*R := by convert hs.trans hb using 1 <;> dsimp [δ,R,W₁] <;> ring
      _ ≤ _ := scale Mo R hMoM hR0
  have hp_bound : (∑ x ∈ Egood, (w x.2*‖completeCubicSum F x.1 x.2‖)*
      (CubeFreeFixedFrequency.conductor h x.1 x.2)^((1 : ℝ)/2)) ≤ X*T^10*P₁ := by
    have hb := hpositive D hD u L hL m Egood w P hgood hP0
      (fun x hx => hmajor x.2 (hE x (hEgood hx)).2.2)
    calc
      _ ≤ Mp*δ*(D^((13 : ℝ)/2)*T^10*P₁) := by
        convert hb using 1 <;> dsimp [δ,T,P₁] <;> ring
      _ ≤ U*(D^((13 : ℝ)/2)*T^10*P₁) := scale Mp _ hMpM (by positivity)
      _ = _ := by dsimp [X]; ring
  have hi_bound : (∑ x ∈ Egood, (w x.2*‖completeCubicSum F x.1 x.2‖)/
      CubeFreeFixedFrequency.conductor h x.1 x.2) ≤ X*W₁ := by
    have hwg : ∀ v ∈ Vgood, 0 ≤ w v := fun v hv => hw v (Finset.mem_filter.mp hv).1
    have hvg : ∀ v ∈ Vgood, GoodFrequency F f tables v := fun v hv => (Finset.mem_filter.mp hv).2
    have hs := FiniteWeightedClassSum.sum_subset_product_le Egood (CubeFreeNonzeroAverage.window D) Vgood
      (fun q v => w v*(‖completeCubicSum F q v‖ / CubeFreeFixedFrequency.conductor h q v))
      (fun x hx => Finset.mem_product.mpr ⟨(hE x (hEgood hx)).1,
        Finset.mem_filter.mpr ⟨(hE x (hEgood hx)).2.2,(hgood x hx).good⟩⟩)
      (fun q _ v hv => mul_nonneg (hwg v hv)
        (div_nonneg (norm_nonneg _) (zero_le_one.trans (CubeFreeFixedFrequency.one_le_conductor h q v))))
    have hb := hinverse D hD u L hL0 m Vgood w hwg
      (fun v hv => (hV v (Finset.mem_filter.mp hv).1).2) hvg
    have hmasses : (∑ v ∈ Vgood, w v) ≤ W₁ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun v hv _ => hw v hv)
    calc
      _ = ∑ x ∈ Egood, w x.2*(‖completeCubicSum F x.1 x.2‖ /
          CubeFreeFixedFrequency.conductor h x.1 x.2) := by simp only [mul_div_assoc]
      _ ≤ Mi*δ*D^((13 : ℝ)/2)*(∑ v ∈ Vgood, w v) := hs.trans hb
      _ ≤ Mi*δ*D^((13 : ℝ)/2)*W₁ :=
        mul_le_mul_of_nonneg_left hmasses (by have hi0 := zero_le_one.trans hMi; positivity)
      _ = Mi*δ*(D^((13 : ℝ)/2)*W₁) := by ring
      _ ≤ U*(D^((13 : ℝ)/2)*W₁) := scale Mi _ hMiM (by positivity)
      _ = _ := by dsimp [X]; ring
  have hg_bound : (∑ x ∈ Egood, w x.2*‖completeCubicSum F x.1 x.2‖) ≤ U*G := by
    have hh := PlanAlphaHolderNumerics.sum_le Egood
      (fun x => w x.2*‖completeCubicSum F x.1 x.2‖)
      (fun x => CubeFreeFixedFrequency.conductor h x.1 x.2)
      (fun x hx => mul_nonneg (hw x.2 (hE x (hEgood hx)).2.2) (norm_nonneg _))
      (fun x _ => CubeFreeFixedFrequency.one_le_conductor h x.1 x.2)
      X T P₁ W₁ hX0 hT0 hP₁ hW₁ hp_bound hi_bound
    convert hh using 1 <;> dsimp [X,G] <;> ring
  have hsplit : (∑ x ∈ E, w x.2*‖completeCubicSum F x.1 x.2‖) =
      (∑ x ∈ Ebad, w x.2*‖completeCubicSum F x.1 x.2‖)+
      (∑ x ∈ Egood, w x.2*‖completeCubicSum F x.1 x.2‖) := by
    dsimp only [Ebad,Egood]
    rw [add_comm,Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  exact PlanAlphaHolderNumerics.add_le_min_add _ _ U A R G hU0 hc_bound ho_bound hg_bound

end CubicTenVariables.PlanAlphaWeightedReduced
