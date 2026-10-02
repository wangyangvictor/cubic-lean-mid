import CubicTenVariables.ConductorMeanFiber
import CubicTenVariables.ConductorResidueMoment
import CubicTenVariables.ConductorRadicalWeightSum

/-! The direct positive conductor moment. The numerical conductor is always
evaluated at the original integer frequency. Its square-root weight is constant
on each fixed-frequency, fixed-high-radical fiber, so the proved residue 3/2
moment applies directly, without a conductor-band decomposition. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.ConductorPositiveMoment
open MvPolynomial HessianTheorem11 ProjectiveMicrolocalData
open NumericalPrimeDepth ConductorMeanDomain
open scoped BigOperators

variable {t N d : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
  {C : ℝ} {h : CoarseBounds F C}

/-- The square-root conductor weight converts the unweighted estimate on a
fixed high-radical fiber into the actual 3/2 moment over its frequencies. -/
theorem exists_fiber_bound (hhom : F.IsHomogeneous 3)
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ (D : ℝ) (m : ℕ) (u : Fin 10 → ℝ) (L : ℝ) (v₀ : Fin 10 → ℤ),
        1 ≤ D → 0 ≤ L → ∀ (r : ℕ × ℕ) (Q : Finset Sample),
        (∀ x ∈ Q, InWindow h f tables D 1 m u L v₀ x) →
        (∀ x ∈ Q, tag h x = r) →
        (∑ x ∈ Q, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖ *
          (NumericalConductor.K h x.1.1 x.1.2 x.2)^((1 : ℝ)/2)) ≤
          M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((13 : ℝ)/2)*
            C^(r.1.primeFactors.card+r.2.primeFactors.card)*
              ∑ v ∈ Q.image Prod.snd, (NumericalConductor.K h r.1 r.2 v)^((3 : ℝ)/2) := by
  classical
  obtain ⟨M,hM,hbound⟩ := ConductorMeanFiber.exists_bound hhom hc ε hε
  refine ⟨M,hM,?_⟩
  intro D m u L v₀ hD hL r Q hQ htag
  have hfiber (v : Fin 10 → ℤ) (hv : v ∈ Q.image Prod.snd) :
      (∑ x ∈ Q.filter (fun x => x.2=v),
        ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖ *
          (NumericalConductor.K h x.1.1 x.1.2 x.2)^((1 : ℝ)/2)) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((13 : ℝ)/2)*
          C^(r.1.primeFactors.card+r.2.primeFactors.card)*
            (NumericalConductor.K h r.1 r.2 v)^((3 : ℝ)/2) := by
    let S : Finset Sample := Q.filter (fun x => x.2=v)
    have hSQ (x : Sample) (hx : x ∈ S) := (Finset.mem_filter.mp hx).1
    have hSv (x : Sample) (hx : x ∈ S) : x.2=v := (Finset.mem_filter.mp hx).2
    have himage : S.image Prod.snd = {v} := by
      apply Finset.ext
      intro w
      constructor
      · intro hw
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
        exact Finset.mem_singleton.mpr (hSv x hx)
      · intro hw
        have hwv : w=v := Finset.mem_singleton.mp hw
        subst w
        obtain ⟨x,hx,hxv⟩ := Finset.mem_image.mp hv
        exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hxv⟩,hxv⟩
    have hs := hbound D 1 m u L v₀ hD hL r S
      (fun x hx => hQ x (hSQ x hx)) (fun x hx => htag x (hSQ x hx))
    rw [himage,Finset.sum_singleton] at hs
    have heq (x : Sample) (hx : x ∈ S) :
        NumericalConductor.K h x.1.1 x.1.2 x.2 = NumericalConductor.K h r.1 r.2 v := by
      rw [tag_conductor h x,htag x (hSQ x hx),hSv x hx]
    have hpow : NumericalConductor.K h r.1 r.2 v *
        (NumericalConductor.K h r.1 r.2 v)^((1 : ℝ)/2) =
        (NumericalConductor.K h r.1 r.2 v)^((3 : ℝ)/2) := by
      calc
        _ = (NumericalConductor.K h r.1 r.2 v)^((1 : ℝ)+(1 : ℝ)/2) := by
          rw [Real.rpow_add (NumericalConductor.K_pos h r.1 r.2 v),Real.rpow_one]
        _ = _ := by norm_num
    change (∑ x ∈ S, _) ≤ _
    calc
      _ = (∑ x ∈ S, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖) *
          (NumericalConductor.K h r.1 r.2 v)^((1 : ℝ)/2) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x hx => by rw [heq x hx]
      _ ≤ (M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((13 : ℝ)/2)*
          C^(r.1.primeFactors.card+r.2.primeFactors.card)*NumericalConductor.K h r.1 r.2 v) *
          (NumericalConductor.K h r.1 r.2 v)^((1 : ℝ)/2) :=
        mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg (NumericalConductor.K_pos h r.1 r.2 v).le _)
      _ = _ := by rw [mul_assoc,hpow]
  calc
    _ = ∑ v ∈ Q.image Prod.snd, ∑ x ∈ Q.filter (fun x => x.2=v),
        ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖ *
          (NumericalConductor.K h x.1.1 x.1.2 x.2)^((1 : ℝ)/2) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) _
    _ ≤ ∑ v ∈ Q.image Prod.snd,
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((13 : ℝ)/2)*
          C^(r.1.primeFactors.card+r.2.primeFactors.card)*
            (NumericalConductor.K h r.1 r.2 v)^((3 : ℝ)/2) := Finset.sum_le_sum hfiber
    _ = _ := (Finset.mul_sum ..).symm

/-- The literal positive half-moment, with one constant before all modulus
scales and translated progression boxes. There is no conductor-band restriction;
the residue moment is applied directly to each actual high-radical fiber. -/
theorem exists_bound (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {B : ℕ} (hgeo : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N)
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (D : ℝ) (m : ℕ) (u : Fin 10 → ℝ) (L : ℝ)
      (v₀ : Fin 10 → ℤ), 1 ≤ D → 0 < m → 0 ≤ L →
      ∀ Q : Finset Sample,
      (∀ x ∈ Q, InWindow h f tables D 1 m u L v₀ x) →
      (∑ x ∈ Q, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖ *
        (NumericalConductor.K h x.1.1 x.1.2 x.2)^((1 : ℝ)/2)) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*(1+L/(m : ℝ))^10*D^((13 : ℝ)/2) := by
  classical
  obtain ⟨A,hA,hmoment⟩ := ConductorResidueMoment.exists_bound lit hgeo hhom hAn hData hN hc
  obtain ⟨M₀,hM₀,hfiber⟩ := exists_fiber_bound hhom hc (ε/2) (by linarith)
  have hC : 1 ≤ C := h.constant_pos
  have hCA : 1 ≤ C*A := by nlinarith
  obtain ⟨M₁,hM₁,hradical⟩ := ConductorRadicalWeightSum.exists_bound (C*A) hCA (ε/2) (by linarith)
  refine ⟨M₀*7^10*M₁,?_,?_⟩
  · have : (1 : ℝ) ≤ M₀*7^10 := by nlinarith
    nlinarith
  intro D m u L v₀ hD hm hL Q hQ
  let Tbox : ℝ := 1+L/(m : ℝ)
  let Hbox : ℝ := 2+‖u‖+L+(m : ℝ)
  let R : Finset (ℕ × ℕ) := Q.image (tag h)
  let fiber (r : ℕ × ℕ) : Finset Sample := Q.filter (fun x => tag h x = r)
  let frequencies (r : ℕ × ℕ) : Finset (Fin 10 → ℤ) := (fiber r).image Prod.snd
  let Z : ℝ := M₀*(D*Hbox)^(ε/2)*D^((13 : ℝ)/2)*7^10*Tbox^10
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hT : 1 ≤ Tbox := by dsimp [Tbox]; linarith [div_nonneg hL hmR.le]
  have hTpos : 0 < Tbox := zero_lt_one.trans_le hT
  have hH : 0 ≤ Hbox := by dsimp [Hbox]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hfiberQ (r : ℕ × ℕ) (x : Sample) (hx : x ∈ fiber r) :
      InWindow h f tables D 1 m u L v₀ x := hQ x (Finset.mem_filter.mp hx).1
  have hfiberTag (r : ℕ × ℕ) (x : Sample) (hx : x ∈ fiber r) : tag h x = r :=
    (Finset.mem_filter.mp hx).2
  have hR (r : ℕ × ℕ) (hr : r ∈ R) :
      1 ≤ r.1 ∧ 1 ≤ r.2 ∧ ((r.1*r.2 : ℕ) : ℝ) ≤ Tbox := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨(tag_positive h x).1,(tag_positive h x).2,(hQ x hx).tag_cutoff⟩
  have hpoint (r : ℕ × ℕ) (hr : r ∈ R) :
      (∑ x ∈ fiber r, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖ *
        (NumericalConductor.K h x.1.1 x.1.2 x.2)^((1 : ℝ)/2)) ≤
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
    have hmomentR := hmoment r.1 r.2 hsf.1 hsf.2 hcop m hm hmco u L hL
      (hR r hr).2.2 v₀ (frequencies r) hbox hres hpdepth hsdepth
    have hf := hfiber D m u L v₀ hD hL r (fiber r) (hfiberQ r) (hfiberTag r)
    calc
      _ ≤ M₀*(D*Hbox)^(ε/2)*D^((13 : ℝ)/2)*
          C^(r.1.primeFactors.card+r.2.primeFactors.card)*
          (∑ v ∈ frequencies r, (NumericalConductor.K h r.1 r.2 v)^((3 : ℝ)/2)) := hf
      _ ≤ M₀*(D*Hbox)^(ε/2)*D^((13 : ℝ)/2)*
          C^(r.1.primeFactors.card+r.2.primeFactors.card)*
          (7^10*A^(r.1.primeFactors.card+r.2.primeFactors.card)*
            Tbox^10/((r.1 : ℝ)^2*(r.2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hmomentR (by positivity)
      _ = _ := by dsimp [Z]; rw [mul_pow]; simp only [div_eq_mul_inv]; ring
  have hsum := hradical Tbox hT R hR
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hTH : Tbox ≤ Hbox := by
    have hdiv : L/(m : ℝ) ≤ L := (div_le_iff₀ hmR).mpr (by nlinarith)
    dsimp [Tbox,Hbox]
    linarith [norm_nonneg u]
  have hTDH : Tbox ≤ D*Hbox := hTH.trans (le_mul_of_one_le_left hH hD)
  have hDH : 0 < D*Hbox := hTpos.trans_le hTDH
  have hpow : (D*Hbox)^(ε/2)*Tbox^(ε/2) ≤ (D*Hbox)^ε := by
    calc
      _ ≤ (D*Hbox)^(ε/2)*(D*Hbox)^(ε/2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow hTpos.le hTDH (by linarith)
        · exact Real.rpow_nonneg hDH.le _
      _ = _ := by rw [← Real.rpow_add hDH]; congr 1; ring
  calc
    _ = ∑ r ∈ R, ∑ x ∈ fiber r, ‖completeCubicSum F (x.1.1*x.1.2^2) x.2‖ *
        (NumericalConductor.K h x.1.1 x.1.2 x.2)^((1 : ℝ)/2) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx) _
    _ ≤ ∑ r ∈ R, Z*((C*A)^(r.1.primeFactors.card+r.2.primeFactors.card)/
        ((r.1 : ℝ)^2*(r.2 : ℝ))) := Finset.sum_le_sum hpoint
    _ = Z*(∑ r ∈ R, (C*A)^(r.1.primeFactors.card+r.2.primeFactors.card)/
        ((r.1 : ℝ)^2*(r.2 : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ Z*(M₁*Tbox^(ε/2)) := mul_le_mul_of_nonneg_left hsum hZ
    _ = (M₀*7^10*M₁)*((D*Hbox)^(ε/2)*Tbox^(ε/2))*Tbox^10*
        D^((13 : ℝ)/2) := by dsimp [Z]; ring
    _ ≤ (M₀*7^10*M₁)*(D*Hbox)^ε*Tbox^10*D^((13 : ℝ)/2) := by
      gcongr

end CubicTenVariables.ConductorPositiveMoment
