import CubicTenVariables.ConductorMeanFiber
import CubicTenVariables.ConductorResidueMoment
import CubicTenVariables.ConductorRadicalWeightSum

/-! The positive conductor mean, retaining the actual numerical depths
at each integer frequency. The proof groups by the two high-depth radicals,
applies the proved 3/2 moment, and sums the resulting reciprocal weights. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.ConductorPositiveMean
open MvPolynomial HessianTheorem11 ProjectiveMicrolocalData
open NumericalPrimeDepth ConductorMeanDomain
open scoped BigOperators

variable {t N d : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
  {C : ℝ} {h : CoarseBounds F C}

/-- One constant precedes every modulus scale, conductor threshold,
translated progression box, and finite family of admissible actual terms.
The assembly retains the proved prime-field count interface as an explicit
argument; its support counts are proved internally. -/
theorem exists_bound (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {B : ℕ} (hgeo : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N)
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (D K0 : ℝ) (m : ℕ) (u : Fin 10 → ℝ) (L : ℝ)
      (v₀ : Fin 10 → ℤ), 1 ≤ D → 1 ≤ K0 → 0 < m → 0 ≤ L →
      ∀ Q : Finset Sample,
      (∀ x ∈ Q, InWindow h f tables D K0 m u L v₀ x) →
      (∑ x ∈ Q, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*(1+L/(m : ℝ))^(10+ε)*
          D^((13 : ℝ)/2)*K0^(-(1 : ℝ)/2) := by
  classical
  obtain ⟨A,hA,hmoment⟩ := ConductorResidueMoment.exists_bound lit hgeo hhom hAn hData hN hc
  obtain ⟨M₀,hM₀,hfiber⟩ := ConductorMeanFiber.exists_bound hhom hc ε hε
  have hC : 1 ≤ C := h.constant_pos
  have hCA : 1 ≤ C*A := by nlinarith
  obtain ⟨M₁,hM₁,hradical⟩ := ConductorRadicalWeightSum.exists_bound (C*A) hCA ε hε
  refine ⟨M₀*7^10*M₁,?_,?_⟩
  · have : (1 : ℝ) ≤ M₀*7^10 := by nlinarith
    nlinarith
  intro D K0 m u L v₀ hD hK0 hm hL Q hQ
  let Tbox : ℝ := 1+L/(m : ℝ)
  let Hbox : ℝ := 2+‖u‖+L+(m : ℝ)
  let R : Finset (ℕ × ℕ) := Q.image (tag h)
  let fiber (r : ℕ × ℕ) : Finset Sample := Q.filter (fun x => tag h x = r)
  let frequencies (r : ℕ × ℕ) : Finset (Fin 10 → ℤ) := (fiber r).image Prod.snd
  let Z : ℝ := M₀*(D*Hbox)^ε*D^((13 : ℝ)/2)*K0^(-(1 : ℝ)/2)*7^10*Tbox^10
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hT : 1 ≤ Tbox := by dsimp [Tbox]; linarith [div_nonneg hL hmR.le]
  have hTpos : 0 < Tbox := zero_lt_one.trans_le hT
  have hH : 0 ≤ Hbox := by dsimp [Hbox]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hK0pos : 0 < K0 := zero_lt_one.trans_le hK0
  have hfiberQ (r : ℕ × ℕ) (x : Sample) (hx : x ∈ fiber r) :
      InWindow h f tables D K0 m u L v₀ x := hQ x (Finset.mem_filter.mp hx).1
  have hfiberTag (r : ℕ × ℕ) (x : Sample) (hx : x ∈ fiber r) : tag h x = r :=
    (Finset.mem_filter.mp hx).2
  have hR (r : ℕ × ℕ) (hr : r ∈ R) :
      1 ≤ r.1 ∧ 1 ≤ r.2 ∧ ((r.1*r.2 : ℕ) : ℝ) ≤ Tbox := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨(tag_positive h x).1,(tag_positive h x).2,(hQ x hx).tag_cutoff⟩
  have hpoint (r : ℕ × ℕ) (hr : r ∈ R) :
      (∑ x ∈ fiber r, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) ≤
        Z*((C*A)^(r.1.primeFactors.card+r.2.primeFactors.card)/
          ((r.1 : ℝ)^2*(r.2 : ℝ))) := by
    obtain ⟨x₀,hx₀,he₀⟩ := Finset.mem_image.mp hr
    have hx₀w := hQ x₀ hx₀
    have hsf : Squarefree r.1 ∧ Squarefree r.2 := by
      simpa only [he₀] using hx₀w.tag_squarefree
    have hcop : r.1.Coprime r.2 := by simpa only [he₀] using hx₀w.tag_coprime
    have hmco : m.Coprime (r.1*r.2) := by
      simpa only [he₀] using hx₀w.tag_modulus_coprime
    have hfreq (v : Fin 10 → ℤ) (hv : v ∈ frequencies r) :
        ∃ x ∈ fiber r, x.2 = v := Finset.mem_image.mp hv
    have hbox (v : Fin 10 → ℤ) (hv : v ∈ frequencies r) :
        ∀ i, |(v i : ℝ)-u i| ≤ L := by
      obtain ⟨x,hx,rfl⟩ := hfreq v hv
      exact (hfiberQ r x hx).box
    have hres (v : Fin 10 → ℤ) (hv : v ∈ frequencies r) :
        ∀ i, (m : ℤ) ∣ v i-v₀ i := by
      obtain ⟨x,hx,rfl⟩ := hfreq v hv
      exact (hfiberQ r x hx).residue
    have hpdepth (v : Fin 10 → ℤ) (hv : v ∈ frequencies r)
        (p : ℕ) (hp : p ∈ r.1.primeFactors) :
        2 ≤ NumericalConductor.primeDepth h p v := by
      obtain ⟨x,hx,rfl⟩ := hfreq v hv
      exact tag_prime_depth h x p (by simpa only [hfiberTag r x hx] using hp)
    have hsdepth (v : Fin 10 → ℤ) (hv : v ∈ frequencies r)
        (p : ℕ) (hp : p ∈ r.2.primeFactors) :
        2 ≤ NumericalConductor.squareDepth h p v := by
      obtain ⟨x,hx,rfl⟩ := hfreq v hv
      exact tag_square_depth h x p (by simpa only [hfiberTag r x hx] using hp)
    have hthreshold (v : Fin 10 → ℤ) (hv : v ∈ frequencies r) :
        K0 ≤ NumericalConductor.K h r.1 r.2 v := by
      obtain ⟨x,hx,rfl⟩ := hfreq v hv
      have hk := (hfiberQ r x hx).conductor_lower
      rw [tag_conductor h x,hfiberTag r x hx] at hk
      exact hk
    have hmomentR := hmoment r.1 r.2 hsf.1 hsf.2 hcop m hm hmco u L hL
      (hR r hr).2.2 v₀ (frequencies r) hbox hres hpdepth hsdepth
    have hKsum : (∑ v ∈ frequencies r, NumericalConductor.K h r.1 r.2 v) ≤
        K0^(-(1 : ℝ)/2)*(7^10*A^(r.1.primeFactors.card+r.2.primeFactors.card)*
          Tbox^10/((r.1 : ℝ)^2*(r.2 : ℝ))) := by
      calc
        _ ≤ ∑ v ∈ frequencies r,
            K0^(-(1 : ℝ)/2)*(NumericalConductor.K h r.1 r.2 v)^((3 : ℝ)/2) :=
          Finset.sum_le_sum fun v hv => ConductorPositiveMeanNumerics.le_scaled_moment
            _ _ hK0pos (hthreshold v hv)
        _ = K0^(-(1 : ℝ)/2)*
            (∑ v ∈ frequencies r, (NumericalConductor.K h r.1 r.2 v)^((3 : ℝ)/2)) := by
          rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hmomentR (by positivity)
    have hf := hfiber D K0 m u L v₀ hD hL r (fiber r) (hfiberQ r) (hfiberTag r)
    calc
      _ ≤ M₀*(D*Hbox)^ε*D^((13 : ℝ)/2)*
          C^(r.1.primeFactors.card+r.2.primeFactors.card)*
          (∑ v ∈ frequencies r, NumericalConductor.K h r.1 r.2 v) := hf
      _ ≤ M₀*(D*Hbox)^ε*D^((13 : ℝ)/2)*
          C^(r.1.primeFactors.card+r.2.primeFactors.card)*
          (K0^(-(1 : ℝ)/2)*(7^10*A^(r.1.primeFactors.card+r.2.primeFactors.card)*
            Tbox^10/((r.1 : ℝ)^2*(r.2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hKsum (by positivity)
      _ = _ := by dsimp [Z]; rw [mul_pow]; simp only [div_eq_mul_inv]; ring
  have hsum := hradical Tbox hT R hR
  have hpow : Tbox^10*Tbox^ε = Tbox^(10+ε) := by
    rw [← Real.rpow_natCast Tbox 10,← Real.rpow_add hTpos]
    norm_num
  calc
    _ = ∑ r ∈ R, ∑ x ∈ fiber r, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖ := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx) _
    _ ≤ ∑ r ∈ R, Z*((C*A)^(r.1.primeFactors.card+r.2.primeFactors.card)/
        ((r.1 : ℝ)^2*(r.2 : ℝ))) := Finset.sum_le_sum hpoint
    _ = Z*(∑ r ∈ R, (C*A)^(r.1.primeFactors.card+r.2.primeFactors.card)/
        ((r.1 : ℝ)^2*(r.2 : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ Z*(M₁*Tbox^ε) := mul_le_mul_of_nonneg_left hsum hZ
    _ = (M₀*7^10*M₁)*(D*Hbox)^ε*(Tbox^10*Tbox^ε)*
        D^((13 : ℝ)/2)*K0^(-(1 : ℝ)/2) := by dsimp [Z]; ring
    _ = _ := by rw [hpow]

end CubicTenVariables.ConductorPositiveMean
