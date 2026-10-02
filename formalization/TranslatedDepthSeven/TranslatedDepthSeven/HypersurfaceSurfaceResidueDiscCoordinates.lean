import TranslatedDepthSeven.HypersurfaceSurfaceResidueDisc

/-! The literal hypersurface construction at any nonsingular coordinate. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

/-- Relabel the ambient coordinates of an actual residue disc. -/
def hypersurfaceResidueDiscUnpermute {ι : Type*} {p E : ℕ} {hE : 0 < E}
    {y : ι → Fin 3 → ℤ} (e : Fin 3 ≃ Fin 3)
    (d : SurfaceNormalizationResidueDisc (Fin 3) ι p E hE (fun j i => y j (e i))) :
    SurfaceNormalizationResidueDisc (Fin 3) ι p E hE y where
  Chart := d.Chart
  ambient := d.ambient.comp (MvPolynomial.rename e.symm).toRingHom
  center := d.center
  parameters := d.parameters
  congruent := d.congruent
  point := d.point
  point_base := d.point_base
  specialization := d.specialization
  specialization_base := d.specialization_base
  specialization_reduction := d.specialization_reduction
  specialization_ambient j := by
    rw [← RingHom.comp_assoc, d.specialization_ambient]
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp

/-- Any nonzero partial at the common residue point yields the actual
formally etale surface chart, using the other two coordinates as parameters. -/
def surfaceHypersurfaceResidueDiscAt {ι : Type*} [Nonempty ι]
    (p E : ℕ) (hp : p.Prime) (hE : 0 < E)
    (F : SurfaceHypersurfacePolynomial) (y : ι → Fin 3 → ℤ) (z : Fin 3 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (hyz : ∀ j i, (p : ℤ) ∣ y j i - z i)
    (v : Fin 3)
    (hzJ : (MvPolynomial.eval z (MvPolynomial.pderiv v F) : ZMod p) ≠ 0) :
    SurfaceNormalizationResidueDisc (Fin 3) ι p E hE y := by
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 v
  have heval (x : Fin 3 → ℤ) (G : SurfaceHypersurfacePolynomial) :
      MvPolynomial.eval (fun i => x (e i)) (MvPolynomial.rename e.symm G) =
        MvPolynomial.eval x G := by
    rw [MvPolynomial.eval_rename]
    simp only [Function.comp_def, Equiv.apply_symm_apply]
  have hderiv : MvPolynomial.pderiv 0 (MvPolynomial.rename e.symm F) =
      MvPolynomial.rename e.symm (MvPolynomial.pderiv v F) := by
    simpa [e] using MvPolynomial.pderiv_rename e.symm.injective v F
  apply hypersurfaceResidueDiscUnpermute e
  apply surfaceHypersurfaceResidueDiscOfNonempty p E hp hE
    (MvPolynomial.rename e.symm F) (fun j i => y j (e i)) (fun i => z (e i))
  · intro j
    rw [heval, hyF]
  · intro j i
    exact hyz j (e i)
  · rw [hderiv, heval]
    exact hzJ

end
end TranslatedDepthSeven
