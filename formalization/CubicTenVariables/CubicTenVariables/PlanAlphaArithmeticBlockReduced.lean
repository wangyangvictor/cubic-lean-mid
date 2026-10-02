import CubicTenVariables.PlanAlphaMixedBlockReduced
import CubicTenVariables.PlanAlphaBlockNumerics
import CubicTenVariables.PlanAlphaMajorantMasses
import CubicTenVariables.PlanAlphaParameterRatios
import CubicTenVariables.LocalizedCompositeMajorant
import CubicTenVariables.CubeFullResidueMajorant

/-! An actual finite arithmetic block in the mixed-modulus argument.
The residue majorants and all three mass estimates are constructed inside
the proof. The Smith cutoff precedes the fixed localization data and epsilon;
the final constant precedes every factor, scale, box, and sample restriction.
This is a block estimate, not the remaining global reindexing and summation. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.PlanAlphaArithmeticBlockReduced
open MvPolynomial HessianTheorem11 NumericalPrimeDepth
open CubeFullSmithParameters (A CubeFull)
open CubefullSmithWeightLocal (omega)
open PlanAlphaMixedWeight (weight)
open IntegerResidueClasses (residue)
open ComplementCubeFreePiece (Sample)
open scoped BigOperators Classical

private theorem scale_bounds (g D X Q : ℝ) (hg : 1 ≤ g) (hD : 1 ≤ D)
    (hX : 1 ≤ X) (hsize : g*D*X ≤ 2*Q) :
    D ≤ 2*Q ∧ X ≤ 2*Q ∧ g*X ≤ 2*Q := by
  have hg0 : 0 ≤ g := zero_le_one.trans hg
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hDX : D ≤ g*D*X := by
    calc
      D = 1*D*1 := by ring
      _ ≤ g*D*X := mul_le_mul (mul_le_mul_of_nonneg_right hg hD0) hX (by positivity) (by positivity)
  have hXX : X ≤ g*D*X := by
    calc
      X = (1*1)*X := by ring
      _ ≤ g*D*X := mul_le_mul_of_nonneg_right
        (mul_le_mul hg hD (by norm_num) hg0) hX0
  have hgX : g*X ≤ g*D*X := by
    calc
      g*X = g*1*X := by ring
      _ ≤ g*D*X := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hg0) hX0
  exact ⟨hDX.trans hsize,hXX.trans hsize,hgX.trans hsize⟩

private theorem box_power_bound (Q X : ℝ) (hQ : 1 ≤ Q) (hX : 0 ≤ X)
    (hXQ : X ≤ 2*Q) :
    (Q^((1 : ℝ)/3)+X^((1 : ℝ)/3))^10 ≤ (3 : ℝ)^10*Q^((10 : ℝ)/3) := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have ht : (2 : ℝ)^((1 : ℝ)/3) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 : ℝ)/3 ≤ 1)
  have hx := Real.rpow_le_rpow hX hXQ (by norm_num : (0 : ℝ) ≤ 1/3)
  rw [Real.mul_rpow (by norm_num) hQ0] at hx
  have hx' : X^((1 : ℝ)/3) ≤ 2*Q^((1 : ℝ)/3) :=
    hx.trans (mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hQ0 _))
  calc
    _ ≤ (3*Q^((1 : ℝ)/3))^10 :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    _ = _ := by rw [mul_pow,←Real.rpow_mul_natCast hQ0]; norm_num

private theorem height_bound (g D X Q B U : ℝ)
    (hg : 1 ≤ g) (hD : 1 ≤ D) (hX : 1 ≤ X) (hQ : 1 ≤ Q) (hB : 1 ≤ B)
    (hU : U ≤ B) (hsize : g*D*X ≤ 2*Q) :
    D*(2+U+Q^((1 : ℝ)/3)+2*g*X) ≤ 16*(B*Q)^2 := by
  have hs := scale_bounds g D X Q hg hD hX hsize
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hroot : Q^((1 : ℝ)/3) ≤ Q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hQ (by norm_num : (1 : ℝ)/3 ≤ 1)
  have hBQ : B ≤ B*Q := by simpa using mul_le_mul_of_nonneg_left hQ hB0
  have hQB : Q ≤ B*Q := by simpa using mul_le_mul_of_nonneg_right hB hQ0
  have hBQ1 : 1 ≤ B*Q := one_le_mul_of_one_le_of_one_le hB hQ
  have hh : 2+U+Q^((1 : ℝ)/3)+2*g*X ≤ 8*(B*Q) := by linarith
  calc
    _ ≤ D*(8*(B*Q)) := mul_le_mul_of_nonneg_left hh (zero_le_one.trans hD)
    _ ≤ (2*Q)*(8*(B*Q)) := mul_le_mul_of_nonneg_right hs.1 (by positivity)
    _ ≤ 16*(B*Q)^2 := by
      have hh := mul_le_mul_of_nonneg_right hQB (mul_nonneg hB0 hQ0)
      nlinarith only [hh]

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C₀ : ℝ} {d₀ : ℕ} {h : CoarseBounds F C₀}

/-- The literal localized sum on a cube-free/cube-full scale block has
the one-ninety-sixth power saving, with explicit epsilon losses. -/
theorem of_data
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C₀ d₀ h)
     (η : ℝ) (hη : 0 < η) :
    ∃ p₀ : ℕ, 3 ≤ p₀ ∧ ∀ (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
      (Dlocal : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F),
      ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 1 ≤ K ∧
      ∀ g : ℕ, 0 < g → g.primeFactors ⊆ s →
      ∀ Q D X : ℝ, 1 ≤ Q → 1 ≤ D → 1 ≤ X →
      (g : ℝ)*D*X ≤ 2*Q → Q ≤ 8*(g : ℝ)*D*X →
      ∀ (u : Fin 10 → ℝ) (B : ℝ), 1 ≤ B → ‖u‖ ≤ B →
      ∀ V : Finset (Fin 10 → ℤ),
      (∀ v ∈ V, v ≠ 0 ∧ ∀ k, |(v k : ℝ)-u k| ≤ Q^((1 : ℝ)/3)) →
      ∀ R : Finset ℕ,
      (∀ r ∈ R, 0 < r ∧ CubeFull r ∧ X ≤ (r : ℝ) ∧ (r : ℝ) ≤ 2*X ∧
        ∀ p ∈ r.primeFactors, p₀ ≤ p) →
      (∀ r : R, (g*PrimeLocalizationSeries.modulus s hprimes Dlocal).Coprime r.val) →
      ∀ E : R → Finset Sample,
      (∀ r x, x ∈ E r → x.1 ∈ CubeFreeNonzeroAverage.window D ∧ x.2 ∈ V ∧
        ((g*r.val)*PrimeLocalizationSeries.modulus s hprimes Dlocal).Coprime x.1 ∧
        x.1.Coprime N) →
      (∑ r : R, ∑ x ∈ E r, ‖localizedCompleteCubicSum F (g*x.1*r.val)
        (PrimeLocalizationSeries.modulus s hprimes Dlocal)
        (PrimeLocalizationSeries.restriction s hprimes Dlocal) x.2‖) ≤
          K*(B*Q)^(2*ε)*Q^((10 : ℝ)-1/96+η+ε) := by
  obtain ⟨p₀,hp₀,hsmith⟩ := CubeFullResidueMajorant.exists_mixed_majorant
     F hhom hAn η hη
  refine ⟨p₀,hp₀,?_⟩
  intro s hprimes Dlocal ε hε
  obtain ⟨Cg,hCg,hgmajor⟩ := LocalizedCompositeMajorant.exists_majorant s hprimes Dlocal hhom
  obtain ⟨Cp,hCp,hgpoint⟩ := LocalizedCompositeMajorant.exists_pointwise_bound s hprimes Dlocal hhom
  obtain ⟨KJ,hKJ,hJbound⟩ := PlanAlphaMajorantMasses.exists_tenth_mass_bound η ε hη.le hε
  obtain ⟨KE,hKE,hEbound⟩ := PlanAlphaMajorantMasses.exists_complement_mass_bound η ε hη.le hε
  obtain ⟨KW,hKW,hWbound⟩ := PlanAlphaMixedWeight.exists_mass_bound F hhom hAn ε hε
  obtain ⟨M,hM,hmixed⟩ := PlanAlphaMixedBlockReduced.of_data
    integrality cubicWeil isolated pointcount hP hhom hAn hc ε hε
  obtain ⟨Knum,hKnum,hnumeric⟩ := PlanAlphaBlockNumerics.exists_bound (η+ε)
    (KJ*Cg) (Cp*KW*3^10) (KE*Cg) (by linarith)
    (one_le_mul_of_one_le_of_one_le hKJ hCg)
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCp hKW) (by norm_num))
    (one_le_mul_of_one_le_of_one_le hKE hCg)
  refine ⟨M*16^ε*Knum,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hM (Real.one_le_rpow (by norm_num) hε.le)) hKnum,?_⟩
  intro g hg hgs Q D X hQ hD hX hsize hsize' u B hB hu V hV R hR hgr E hE
  let W := PrimeLocalizationSeries.modulus s hprimes Dlocal
  let Ω := PrimeLocalizationSeries.restriction s hprimes Dlocal
  let Ag := LocalizedCompositeMajorant.modulus s g
  let m : ℕ → ℕ := fun r => Ag*A r
  letI : NeZero g := ⟨hg.ne'⟩
  letI : NeZero W := ⟨(PrimeLocalizationSeries.modulus_pos s hprimes Dlocal).ne'⟩
  letI : NeZero Ag := ⟨(LocalizedCompositeMajorant.modulus_pos s g).ne'⟩
  have hmpos (r : ℕ) : 0 < m r := Nat.mul_pos (LocalizedCompositeMajorant.modulus_pos s g) (CubeFullSmithParameters.A_pos r)
  letI : ∀ r : R, NeZero (m r.val) := fun r => ⟨(hmpos r.val).ne'⟩
  have hgR : 1 ≤ (g : ℝ) := by exact_mod_cast hg
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hroot : 1 ≤ Q^((1 : ℝ)/3) := Real.one_le_rpow hQ (by norm_num)
  have hscales := scale_bounds (g : ℝ) D X Q hgR hD hX hsize
  have hAgdvd : Ag ∣ g := LocalizedCompositeMajorant.modulus_dvd s g hg hgs
  have hmdvd (r : R) : m r.val ∣ g*r.val :=
    mul_dvd_mul hAgdvd (PlanAlphaParameterRatios.A_dvd r.val (hR r.val r.property).1)
  have hacop (r : R) : Ag.Coprime (A r.val) :=
    Nat.Coprime.of_dvd hAgdvd (PlanAlphaParameterRatios.A_dvd r.val (hR r.val r.property).1)
      (Nat.coprime_mul_iff_left.mp (hgr r)).1
  obtain ⟨Pg,hPg,hPgmajor,hPgmass⟩ := hgmajor g hg hgs V
  choose P hP0 hPmajor hPmass using fun r : R => hsmith r.val
    (hR r.val r.property).1 (hR r.val r.property).2.1
    (hR r.val r.property).2.2.2.2 V g W Ag Ω Pg (hacop r) hPg hPgmajor
  let Pmass : ℕ → ℝ := fun r => if hr : r ∈ R then ∑ b, P ⟨r,hr⟩ b else 0
  let T : ℕ → ℝ := fun r => 1+Q^((1 : ℝ)/3)/(m r : ℝ)
  let Wmass : ℕ → ℝ := fun r => ∑ v ∈ V, weight F g W Ω r v
  have hPm (r : R) : Pmass r.val = ∑ b, P r b := by simp [Pmass,r.property]
  have hPm0 (r : ℕ) (hr : r ∈ R) : 0 ≤ Pmass r := by
    rw [show Pmass r = ∑ b, P ⟨r,hr⟩ b from hPm ⟨r,hr⟩]
    exact Finset.sum_nonneg fun b _ => hP0 ⟨r,hr⟩ b
  have hPmBound (r : ℕ) (hr : r ∈ R) :
      Pmass r ≤ (Cg*(g : ℝ)^((28 : ℝ)/3))*(r : ℝ)^(10+η)*omega r := by
    rw [show Pmass r = ∑ b, P ⟨r,hr⟩ b from hPm ⟨r,hr⟩]
    calc
      _ ≤ (∑ b, Pg b)*((r : ℝ)^(10+η)*omega r) := hPmass ⟨r,hr⟩
      _ ≤ (Cg*(g : ℝ)^((28 : ℝ)/3))*((r : ℝ)^(10+η)*omega r) :=
        mul_le_mul_of_nonneg_right hPgmass (by unfold omega; positivity)
      _ = _ := by ring
  have hWm0 (r : ℕ) : 0 ≤ Wmass r :=
    Finset.sum_nonneg fun v _ => PlanAlphaMixedWeight.weight_nonneg F g W Ω r v
  have hT0 (r : ℕ) : 0 ≤ T r := by dsimp [T]; positivity
  have hTbound (r : ℕ) (hr : r ∈ R) :
      0 ≤ T r ∧ T r ≤ 1+2*D^((1 : ℝ)/3)*CubefullSmithWeightLocal.u r := by
    refine ⟨hT0 r,?_⟩
    have hsizeR : Q ≤ 8*(g : ℝ)*D*(r : ℝ) := hsize'.trans
      (mul_le_mul_of_nonneg_left (hR r hr).2.2.1 (by positivity))
    have hh := PlanAlphaParameterRatios.progression_width_le_two r g Ag Q D
      (hR r hr).1 (LocalizedCompositeMajorant.modulus_pos s g) hQ0 hD0
      (LocalizedCompositeMajorant.le_modulus_cube s hprimes g hg hgs) hsizeR
    simpa only [T,m,Nat.cast_mul] using hh
  have hRsmall : ∀ r ∈ R, 0 < r ∧ CubeFull r ∧ (r : ℝ) ≤ 2*X :=
    fun r hr => ⟨(hR r hr).1,(hR r hr).2.1,(hR r hr).2.2.2.1⟩
  let J : ℝ := ∑ r ∈ R, (T r)^10*Pmass r
  let WM : ℝ := ∑ r ∈ R, Wmass r
  let EM : ℝ := ∑ r ∈ R, min
    (D^((59 : ℝ)/6)*(T r/D^((1 : ℝ)/3)+(T r/D^((1 : ℝ)/3))^9)*Pmass r)
    (D^9*Wmass r)
  have hJ0 : 0 ≤ J := Finset.sum_nonneg fun r hr => mul_nonneg (pow_nonneg (hT0 r) _) (hPm0 r hr)
  have hWM0 : 0 ≤ WM := Finset.sum_nonneg fun r _ => hWm0 r
  have hEM0 : 0 ≤ EM := by
    apply Finset.sum_nonneg
    intro r hr
    exact le_min (by have hp := hPm0 r hr; have ht := hT0 r; positivity)
      (mul_nonneg (pow_nonneg hD0 _) (hWm0 r))
  have hJ := hJbound X hX R hRsmall D hD (Cg*(g : ℝ)^((28 : ℝ)/3))
    (by positivity) Pmass T hPm0 hPmBound hTbound
  have hEMfirst : EM ≤ (KE*Cg)*(g : ℝ)^((28 : ℝ)/3)*X^(10+(η+ε))*D^((59 : ℝ)/6) := by
    have hb := hEbound X hX R hRsmall D hD (Cg*(g : ℝ)^((28 : ℝ)/3))
      (by positivity) Pmass T hPm0 hPmBound hTbound
    calc
      _ ≤ ∑ r ∈ R, D^((59 : ℝ)/6)*
          (T r/D^((1 : ℝ)/3)+(T r/D^((1 : ℝ)/3))^9)*Pmass r :=
        Finset.sum_le_sum fun _ _ => min_le_left _ _
      _ = D^((59 : ℝ)/6)*(∑ r ∈ R,
          (T r/D^((1 : ℝ)/3)+(T r/D^((1 : ℝ)/3))^9)*Pmass r) := by
        simp only [Finset.mul_sum,mul_assoc]
      _ ≤ D^((59 : ℝ)/6)*(KE*(Cg*(g : ℝ)^((28 : ℝ)/3))*X^(10+η+ε)) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hD0 _)
      _ = _ := by rw [add_assoc 10 η ε]; ring
  have hEMsecond : EM ≤ D^9*WM := by
    calc
      _ ≤ ∑ r ∈ R, D^9*Wmass r := Finset.sum_le_sum fun _ _ => min_le_right _ _
      _ = _ := by rw [Finset.mul_sum]
  have hWM := hWbound X hX R hRsmall g W Ω V u (Q^((1 : ℝ)/3))
    (Cp*(g : ℝ)^7) hroot (by positivity) (fun v hv => (hV v hv).2)
    (fun v _ => hgpoint g hg hgs v)
  have hWM' : WM ≤ (Cp*KW*3^10)*(g : ℝ)^7*X^((32 : ℝ)/5+(η+ε))*Q^((10 : ℝ)/3) := by
    have hexp : X^((32 : ℝ)/5+ε) ≤ X^((32 : ℝ)/5+(η+ε)) :=
      Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    calc
      _ ≤ (Cp*(g : ℝ)^7)*KW*X^((32 : ℝ)/5+ε)*
          (Q^((1 : ℝ)/3)+X^((1 : ℝ)/3))^10 := hWM
      _ ≤ (Cp*(g : ℝ)^7)*KW*X^((32 : ℝ)/5+(η+ε))*
          ((3 : ℝ)^10*Q^((10 : ℝ)/3)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hexp (by positivity)
        · exact box_power_bound Q X hQ hX0 hscales.2.1
        · positivity
        · positivity
      _ = _ := by ring
  have hJ' : J ≤ (KJ*Cg)*(g : ℝ)^((28 : ℝ)/3)*X^((121 : ℝ)/12+(η+ε))*D^((10 : ℝ)/3) := by
    convert hJ using 1 <;> rw [add_assoc ((121 : ℝ)/12) η ε] <;> ring
  have hn := hnumeric (g : ℝ) D X Q hgR hD hX hQ hsize hsize'
    J WM EM hJ0 hWM0 hEM0 hJ' hWM' hEMfirst hEMsecond
  have hcap (r : R) : (m r.val : ℝ) ≤ 2*(g : ℝ)*X := by
    have hh : m r.val ≤ g*r.val := Nat.le_of_dvd (Nat.mul_pos hg (hR r.val r.property).1) (hmdvd r)
    calc
      _ ≤ (g : ℝ)*(r.val : ℝ) := by exact_mod_cast hh
      _ ≤ (g : ℝ)*(2*X) := mul_le_mul_of_nonneg_left (hR r.val r.property).2.2.2.1 (Nat.cast_nonneg g)
      _ = _ := by ring
  have hsample (r : R) (x : Sample) (hx : x ∈ E r) :
      x.1 ∈ CubeFreeNonzeroAverage.window D ∧ x.1.Coprime (m r.val*N) ∧
        x.2 ∈ V ∧ ((g*r.val)*W).Coprime x.1 := by
    have he := hE r x hx
    refine ⟨he.1,Nat.coprime_mul_iff_right.mpr ⟨?_,he.2.2.2⟩,he.2.1,he.2.2.1⟩
    exact Nat.Coprime.of_dvd_right ((hmdvd r).trans (dvd_mul_right _ _)) he.2.2.1.symm
  have hb := hmixed D hD u (Q^((1 : ℝ)/3)) hroot g W Ω
    (PrimeLocalizationSeries.restriction_unitInvariant s hprimes Dlocal)
    R (fun r hr => (hR r hr).1) (fun r : R => m r.val) (2*(g : ℝ)*X)
    (by positivity) hcap hgr V P hV hP0 hPmajor E hsample
  change _ ≤ M*(D*(2+‖u‖+Q^((1 : ℝ)/3)+2*(g : ℝ)*X))^ε *
    ((∑ r : R, min (D^((59 : ℝ)/6)*(T r.val/D^((1 : ℝ)/3)+
      (T r.val/D^((1 : ℝ)/3))^9)*(∑ b, P r b)) (D^9*Wmass r.val)) +
      D^((13 : ℝ)/2)*(∑ r : R, (T r.val)^10*(∑ b, P r b))^((2 : ℝ)/3)*
        (∑ r : R, Wmass r.val)^((1 : ℝ)/3)) at hb
  simp only [←hPm,Finset.sum_coe_sort] at hb
  rw [Finset.sum_coe_sort R (fun r : ℕ => min
    (D^((59 : ℝ)/6)*(T r/D^((1 : ℝ)/3)+(T r/D^((1 : ℝ)/3))^9)*Pmass r)
    (D^9*Wmass r)),Finset.sum_coe_sort R (fun r : ℕ => (T r)^10*Pmass r)] at hb
  change _ ≤ M*(D*(2+‖u‖+Q^((1 : ℝ)/3)+2*(g : ℝ)*X))^ε *
    (EM+D^((13 : ℝ)/2)*J^((2 : ℝ)/3)*WM^((1 : ℝ)/3)) at hb
  have hheight : (D*(2+‖u‖+Q^((1 : ℝ)/3)+2*(g : ℝ)*X))^ε ≤
      16^ε*(B*Q)^(2*ε) := by
    have hh := Real.rpow_le_rpow (by positivity)
      (height_bound (g : ℝ) D X Q B ‖u‖ hgR hD hX hQ hB hu hsize) hε.le
    rwa [Real.mul_rpow (by norm_num) (sq_nonneg _),←Real.rpow_natCast_mul (by positivity)] at hh
  calc
    _ ≤ M*(D*(2+‖u‖+Q^((1 : ℝ)/3)+2*(g : ℝ)*X))^ε *
        (EM+D^((13 : ℝ)/2)*J^((2 : ℝ)/3)*WM^((1 : ℝ)/3)) := hb
    _ ≤ (M*(16^ε*(B*Q)^(2*ε)))*(Knum*Q^((10 : ℝ)-1/96+(η+ε))) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hheight (zero_le_one.trans hM)) hn
      · exact add_nonneg hEM0 (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hD0 _) (Real.rpow_nonneg hJ0 _))
          (Real.rpow_nonneg hWM0 _))
      · exact mul_nonneg (zero_le_one.trans hM) (mul_nonneg
          (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg
            (mul_nonneg (zero_le_one.trans hB) hQ0) _))
    _ = _ := by rw [add_assoc ((10 : ℝ)-1/96) η ε]; ring

end CubicTenVariables.PlanAlphaArithmeticBlockReduced
