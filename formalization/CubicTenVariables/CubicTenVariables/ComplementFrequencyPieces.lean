import CubicTenVariables.MicrolocalGenericFrequencyBridge
import CubicTenVariables.OffTerminalFrequencyCertificate

/-! The literal rational complement pieces U₂,...,U₆. The incoming level-one
promotion is placed in U₃, while U₂ is the unpromoted generic set P₀∩Q₀.
All depth exclusions concern the actual geometric incidence. No periodicity
of the numerical prime-square depth is asserted. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.ComplementFrequencyPieces
open MvPolynomial HessianTheorem11 RationalConeClosure ProjectiveMicrolocalData
open MicrolocalPromotedPartition MicrolocalPartitionCounts NumericalPrimeDepth
open scoped BigOperators

variable {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}

/-- Index i represents source level r=i+2. In particular, `tables 0` is
the level-one open U₁, not the level-two open. -/
def piece (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (i : Fin 5) : Set (Fin 10 → ℚ) :=
  if i = 0 then
    part f (promotionFamily (fun a => (tables a).open)) 0 ∩ MicrolocalSquarePartition.part f 0
  else if i = 1 then
    (part f (promotionFamily (fun a => (tables a).open)) 1 ∪ (tables 0).open) \
      OffTerminalFrequencyCertificate.exceptionalSet F
  else part f (promotionFamily (fun a => (tables a).open)) i.castSucc \
    OffTerminalFrequencyCertificate.exceptionalSet F

variable (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))

theorem piece_values :
    piece F f tables 0 = part f (promotionFamily (fun a => (tables a).open)) 0 ∩
      MicrolocalSquarePartition.part f 0 ∧
    piece F f tables 1 = (part f (promotionFamily (fun a => (tables a).open)) 1 ∪
      (tables 0).open) \ OffTerminalFrequencyCertificate.exceptionalSet F ∧
    piece F f tables 2 = part f (promotionFamily (fun a => (tables a).open)) 2 \
      OffTerminalFrequencyCertificate.exceptionalSet F ∧
    piece F f tables 3 = part f (promotionFamily (fun a => (tables a).open)) 3 \
      OffTerminalFrequencyCertificate.exceptionalSet F ∧
    piece F f tables 4 = part f (promotionFamily (fun a => (tables a).open)) 4 \
      OffTerminalFrequencyCertificate.exceptionalSet F := by
  simp [piece]

theorem zero_iff_goodFrequency (v : Fin 10 → ℤ) :
    (fun a => (v a : ℚ)) ∈ piece F f tables 0 ↔
      ConductorFixedFrequency.GoodFrequency F f tables v := by
  simp [piece,ConductorFixedFrequency.GoodFrequency]

private theorem compatible : Compatible f (promotionFamily (fun a => (tables a).open)) :=
  promotionFamily_compatible _ (fun a => (tables a).open_subset_layer (by omega))

private theorem first_open_subset_part_zero : (tables 0).open ⊆
    part f (promotionFamily (fun a => (tables a).open)) 0 := by
  intro x hx
  rw [part_eq_source _ 0 (by decide)]
  refine ⟨Or.inr ?_,?_⟩
  · simpa only [Fin.val_zero,zero_add,promotionFamily_level] using hx
  · intro hz
    have he : x=0 := Set.mem_singleton_iff.mp hz
    exact (tables 0).open_nonzero (he ▸ hx)

/-- Every piece lies in a prime partition level no higher than its index.
The extra U₁ branch of piece 1 lies in P₀. -/
theorem mem_prime_part_le (i : Fin 5) (x : Fin 10 → ℚ)
    (hx : x ∈ piece F f tables i) :
    ∃ j : Fin 6, j.val ≤ i.val ∧
      x ∈ part f (promotionFamily (fun a => (tables a).open)) j := by
  by_cases hi : i=0
  · subst i
    exact ⟨0,by decide,(by simpa only [piece,if_pos rfl] using hx :
      x ∈ part f (promotionFamily (fun a => (tables a).open)) 0 ∩
        MicrolocalSquarePartition.part f 0).1⟩
  · by_cases hi1 : i=1
    · subst i
      have hx' := (by simpa only [piece,show (1 : Fin 5)≠0 by decide,
        if_false,if_pos rfl] using hx : x ∈
        (part f (promotionFamily (fun a => (tables a).open)) 1 ∪ (tables 0).open) \
          OffTerminalFrequencyCertificate.exceptionalSet F)
      rcases hx'.1 with hp | ho
      · exact ⟨1,by decide,hp⟩
      · exact ⟨0,by decide,first_open_subset_part_zero tables ho⟩
    · exact ⟨i.castSucc,le_rfl,(by simpa only [piece,if_neg hi,if_neg hi1] using hx :
        x ∈ part f (promotionFamily (fun a => (tables a).open)) i.castSucc \
          OffTerminalFrequencyCertificate.exceptionalSet F).1⟩

theorem mem_nonzero (i : Fin 5) (x : Fin 10 → ℚ)
    (hx : x ∈ piece F f tables i) : x ≠ 0 := by
  obtain ⟨j,_,hj⟩ := mem_prime_part_le tables i x hx
  exact fun he => hj.2 (Set.mem_singleton_iff.mpr he)

theorem mem_off_exceptional (i : Fin 5) (hi : 1 ≤ i.val) (x : Fin 10 → ℚ)
    (hx : x ∈ piece F f tables i) : x ∉ OffTerminalFrequencyCertificate.exceptionalSet F := by
  have hi0 : i ≠ 0 := by intro he; subst i; simp at hi
  unfold piece at hx
  rw [if_neg hi0] at hx
  split_ifs at hx <;> exact hx.2

private theorem part_avoids_next_next (j : Fin 6) (hj : j.val < 5)
    (x : Fin 10 → ℚ)
    (hx : x ∈ part f (promotionFamily (fun a => (tables a).open)) j) :
    x ∉ filtration f (j.val+2) := by
  rw [part_eq_source _ j hj] at hx
  rcases hx.1 with hp | ho
  · exact fun hz => hp.1.2 (filtration_antitone (by omega) hz)
  · by_cases hj1 : j.val+1 < 5
    · have hl := (compatible tables).2.2 (j.val+1) (by omega) ho
      simp only [PromotedFrequencyPartition.layer,if_pos hj1,Nat.add_assoc] at hl
      exact hl.2
    · have he : j.val+1=5 := by omega
      rw [he,promotionFamily_five] at ho
      exact False.elim ho

/-- The actual geometric depth locus of every level k≥r is avoided.
This also proves the manuscript's finite range r≤k≤6. -/
theorem not_mem_depth (i : Fin 5) (x : Fin 10 → ℚ)
    (hx : x ∈ piece F f tables i) (k : ℕ) (hk : i.val+2 ≤ k) :
    rationalEmbedding x ∉ ProjectiveMicrolocalDepth.depth f k := by
  have hbase : x ∉ filtration f (i.val+2) := by
    by_cases hi : i=0
    · subst i
      have hx' := hx
      rw [(piece_values tables).1,MicrolocalGenericFrequencyBridge.rational_parts_inter_eq tables] at hx'
      intro hz
      exact hx'.2 (ProjectiveMicrolocalDepth.depth_antitone (by decide : 1≤2) hz)
    · by_cases hi1 : i=1
      · subst i
        have hx' := (by simpa only [piece,show (1 : Fin 5)≠0 by decide,
          if_false,if_pos rfl] using hx : x ∈
          (part f (promotionFamily (fun a => (tables a).open)) 1 ∪ (tables 0).open) \
            OffTerminalFrequencyCertificate.exceptionalSet F)
        rcases hx'.1 with hp | ho
        · exact part_avoids_next_next tables 1 (by decide) x hp
        · have hl := (tables 0).open_subset_layer (by decide) ho
          have hn : x ∉ filtration f 2 := hl.2
          exact fun hz => hn (filtration_antitone (by decide : 2≤3) hz)
      · have hp := (by simpa only [piece,if_neg hi,if_neg hi1] using hx :
          x ∈ part f (promotionFamily (fun a => (tables a).open)) i.castSucc \
            OffTerminalFrequencyCertificate.exceptionalSet F).1
        exact part_avoids_next_next tables i.castSucc i.isLt x hp
  have hnot : rationalEmbedding x ∉ ProjectiveMicrolocalDepth.depth f (i.val+2) := by
    simpa only [filtration,show i.val+2≠0 by omega,if_false,rationalPoints] using hbase
  exact fun hz => hnot (ProjectiveMicrolocalDepth.depth_antitone hk hz)

/-- Adjoining the origin to the geometric depth support changes none of
the avoidance conclusions for these punctured rational pieces. -/
theorem not_mem_depth_with_origin (i : Fin 5) (x : Fin 10 → ℚ)
    (hx : x ∈ piece F f tables i) (k : ℕ) (hk : i.val+2 ≤ k) :
    rationalEmbedding x ∉ ({0} ∪ ProjectiveMicrolocalDepth.depth f k) := by
  rintro (hz | hd)
  · exact mem_nonzero tables i x hx ((rationalEmbedding_eq_zero_iff x).mp
      (Set.mem_singleton_iff.mp hz))
  · exact not_mem_depth tables i x hx k hk hd

/-- The bad-section set together with the five literal pieces covers
exactly the nonzero rational frequencies. Disjointness is not needed here. -/
theorem cover (hgeo : Geometry F f) (hhom : F.IsHomogeneous 3) :
    OffTerminalFrequencyCertificate.exceptionalSet F ∪ (⋃ i : Fin 5, piece F f tables i) =
      {x : Fin 10 → ℚ | x ≠ 0} := by
  ext x
  constructor
  · rintro (hB | hx)
    · exact hB.1
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      exact mem_nonzero tables i x hi
  · intro hx
    by_cases hB : x ∈ OffTerminalFrequencyCertificate.exceptionalSet F
    · exact Or.inl hB
    right
    obtain ⟨j,hj,_⟩ := existsUnique_level _ (compatible tables) x hx
    apply Set.mem_iUnion.mpr
    fin_cases j
    · change x ∈ part f (promotionFamily (fun a => (tables a).open)) 0 at hj
      rw [part_eq_source _ 0 (by decide)] at hj
      rcases hj.1 with ho | hu
      · refine ⟨0,?_⟩
        rw [(piece_values tables).1,MicrolocalGenericFrequencyBridge.rational_parts_inter_eq tables]
        exact ⟨hx,ho.1.2⟩
      · refine ⟨1,?_⟩
        rw [(piece_values tables).2.1]
        refine ⟨Or.inr ?_,hB⟩
        simpa only [Fin.val_zero,zero_add,promotionFamily_level] using hu
    · exact ⟨1,by rw [(piece_values tables).2.1]; exact ⟨Or.inl hj,hB⟩⟩
    · exact ⟨2,by rw [(piece_values tables).2.2.1]; exact ⟨hj,hB⟩⟩
    · exact ⟨3,by rw [(piece_values tables).2.2.2.1]; exact ⟨hj,hB⟩⟩
    · exact ⟨4,by rw [(piece_values tables).2.2.2.2]; exact ⟨hj,hB⟩⟩
    · exfalso
      apply hB
      apply (OffTerminalFrequencyCertificate.mem_exceptional_iff F hhom x).mpr
      refine ⟨hx,?_⟩
      rw [part_five] at hj
      exact MicrolocalTerminalDepth.depth_succ_subset_badNormals hgeo 4 hj.1

/-- The cover applies to the literal rational casts of all nonzero
integer frequencies. -/
theorem integer_cover (hgeo : Geometry F f) (hhom : F.IsHomogeneous 3)
    (v : Fin 10 → ℤ) (hv : v ≠ 0) :
    (fun a => (v a : ℚ)) ∈ OffTerminalFrequencyCertificate.exceptionalSet F ∨
      ∃ i : Fin 5, (fun a => (v a : ℚ)) ∈ piece F f tables i := by
  have hq : (fun a => (v a : ℚ)) ≠ 0 := by
    intro he
    apply hv
    funext a
    have ha : (v a : ℚ)=0 := congrFun he a
    exact_mod_cast ha
  have hm : (fun a => (v a : ℚ)) ∈
      OffTerminalFrequencyCertificate.exceptionalSet F ∪ (⋃ i : Fin 5, piece F f tables i) := by
    rw [cover tables hgeo hhom]
    exact hq
  exact hm.elim Or.inl (fun hi => Or.inr (Set.mem_iUnion.mp hi))

/-- All source levels r=2,...,6 have the same polynomial certificate
height constant. At numerical prime depth at least r−1 the prime divides
the certificate; elsewhere the actual prime sum has exponent (9+r)/2. -/
theorem exists_prime_certificate {N d : ℕ} {C : ℝ} {h : CoarseBounds F C}
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d h)
    (i : Fin 5) (v : Fin 10 → ℤ)
    (hv : (fun a => (v a : ℚ)) ∈ piece F f tables i) :
    ∃ Δ : ℕ, 1 ≤ Δ ∧
      (∀ H : ℝ, 1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (Δ : ℝ) ≤ C*H^d) ∧
      (∀ (p : ℕ) [Fact p.Prime], i.val+1 ≤ primeDepth h p v → p ∣ Δ) ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
        ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((9+((i.val+2 : ℕ) : ℝ))/2) := by
  obtain ⟨j,hji,hj⟩ := mem_prime_part_le tables i _ hv
  obtain ⟨Δ,hΔ,hheight,hcert⟩ := hc.prime_certificates j v hj
  have hcert' (p : ℕ) [Fact p.Prime] (hp : i.val+1 ≤ primeDepth h p v) : p ∣ Δ :=
    hcert p (by omega)
  refine ⟨Δ,hΔ,hheight,hcert',?_⟩
  intro p _ hp
  have hd : primeDepth h p v ≤ i.val := by
    by_contra hn
    exact hp (hcert' p (by omega))
  have he : (9+((i.val+2 : ℕ) : ℝ))/2 = (11+(i.val : ℝ))/2 := by
    push_cast
    ring
  rw [he]
  exact (primeDepth_le_iff h p v i.val).mp hd

end CubicTenVariables.ComplementFrequencyPieces
