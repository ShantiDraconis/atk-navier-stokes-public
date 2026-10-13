import Mathlib
import ATK.Exact
import ATK.FCNavierStokes
import ATK.NSBridge

/-!
# ATK — Ponte (D): explosão no toro `ℝ³/ℤ³`

Mesmo formato da ponte (C) (`ATK.NSBridge.clayC_of_fc`):

* **Alvo exato**: `ATK.Exact.ClayD` — para todo `ν > 0` existem dado `u⁰` suave, de divergência
  nula e 1-periódico, e força `f` suave, 1-periódica e com decaimento em `t`, tais que NÃO existe
  solução suave e espacialmente periódica.
* **Hipótese H**: `FCBreakdownPeriodic` — o enunciado `navier_stokes_breakdown_periodic` de
  `openai/NavierStokesAndEuler` (commit `f9e8bc5`, `ComparatorChallenges/NavierStokes.lean`),
  sobre as definições copiadas em `ATK/FCNavierStokes.lean`.
* **Ponte**: `clayD_of_fc : FCBreakdownPeriodic → ATK.Exact.ClayD`.

Única diferença de formalização: a força periódica ATK (`PeriodicForce`) exige periodicidade
espacial para todo `t ∈ ℝ`; a deles, para `t ≥ 0`. Usa-se `extForce f t x = f x (max t 0)`, que
coincide com `f` em `t ≥ 0` (onde a equação, a suavidade e o decaimento são medidos) e é
periódica para todo `t`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Laplacian InnerProductSpace

namespace ATK.NSBridgeD

open ATK.Exact (R3 e pd div3 lap3 grad3 conv3)
open ATK.NSBridge

/-- **Hipótese H** — enunciado (D) no formato OpenAI/Formal Conjectures. -/
def FCBreakdownPeriodic : Prop :=
  ∀ (nu : ℝ), nu > 0 → ∃ (u₀ : R3 → R3) (f : R3 → ℝ → R3),
    NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀ ∧
    NavierStokes.Comparator.ForceConditionPeriodic f ∧
    ¬ (∃ v p, NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p)

/-- Força ATK: `f'(t, x) = f(x, max t 0)`. -/
def extForce (f : R3 → ℝ → R3) : ℝ → R3 → R3 := fun t x => f x (max t 0)

theorem extForce_eq (f : R3 → ℝ → R3) {t : ℝ} (ht : 0 ≤ t) (x : R3) :
    extForce f t x = f x t := by
  simp [extForce, max_eq_left ht]

theorem smoothForce_ext {f : R3 → ℝ → R3}
    (h : ContDiffOn ℝ ∞ (↿f) ((univ : Set R3) ×ˢ Ici (0 : ℝ))) :
    ATK.Exact.SmoothForce (extForce f) := by
  have h1 := smoothForce_of_fc h
  unfold ATK.Exact.SmoothForce at h1 ⊢
  refine h1.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact extForce_eq f ht x

theorem periodicForce_ext {f : R3 → ℝ → R3}
    (hf : NavierStokes.Comparator.ForceConditionPeriodic f) :
    ATK.Exact.PeriodicForce (extForce f) := by
  refine ⟨fun t x j => ?_, fun k K => ?_⟩
  · show f (x + e j) (max t 0) = f x (max t 0)
    exact hf.isOnePeriodic (max t 0) (le_max_right t 0) x j
  · obtain ⟨C, hC⟩ := hf.decay k K
    refine ⟨C, fun t ht x => ?_⟩
    have hEq : EqOn (fun z : ℝ × R3 => extForce f z.1 z.2) (fun z : ℝ × R3 => f z.2 z.1)
        (Ici 0 ×ˢ univ) := by
      rintro ⟨s, y⟩ ⟨hs, -⟩
      exact extForce_eq f hs y
    have hmem : (t, x) ∈ (Ici (0 : ℝ) ×ˢ (univ : Set R3)) := Set.mk_mem_prod ht (mem_univ x)
    rw [iteratedFDerivWithin_congr hEq hmem]
    set g := LinearIsometryEquiv.prodComm ℝ ℝ R3 with hg
    have hs : UniqueDiffOn ℝ ((univ : Set R3) ×ˢ Ici (0 : ℝ)) :=
      uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)
    have hgx : g (t, x) = (x, t) := by
      first
        | rfl
        | simp [hg]
    have hx : g (t, x) ∈ (univ : Set R3) ×ˢ Ici (0 : ℝ) := by
      rw [hgx]
      exact Set.mk_mem_prod (mem_univ x) ht
    have key := g.norm_iteratedFDerivWithin_comp_right (↿f) hs hx k
    have hset : g ⁻¹' ((univ : Set R3) ×ˢ Ici (0 : ℝ)) = Ici (0 : ℝ) ×ˢ (univ : Set R3) := by
      ext ⟨a, b⟩
      simp [hg, and_comm]
    have hfun : (↿f) ∘ g = fun z : ℝ × R3 => f z.2 z.1 := by
      funext z
      first
        | rfl
        | simp [hg]
    rw [hset, hgx, hfun] at key
    rw [key]
    have hpos : (0 : ℝ) < (1 + t) ^ (K : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hb := hC x t ht
    rw [le_div_iff₀ hpos] at hb
    rw [← Real.rpow_natCast]
    calc (1 + t) ^ (K : ℝ) * ‖iteratedFDerivWithin ℝ k (↿f) (univ ×ˢ Ici 0) (x, t)‖
        = ‖iteratedFDerivWithin ℝ k (↿f) (univ ×ˢ Ici 0) (x, t)‖ * (1 + t) ^ (K : ℝ) :=
          mul_comm _ _
      _ ≤ C := hb

/-- Toda solução clássica ATK (com a força estendida) é solução no sentido deles. -/
theorem base_of_classical {ν : ℝ} {u0 : R3 → R3} {f : R3 → ℝ → R3} {u : ℝ → R3 → R3}
    {p : ℝ → R3 → ℝ} (hns : ATK.Exact.NSClassical ν u0 (extForce f) u p) :
    NavierStokes.Comparator.NavierStokesExistenceAndSmoothness ν u0 f
      (fun x t => u t x) (fun x t => p t x) :=
  { navier_stokes := by
      intro x t ht
      have hm := hns.momentum t ht x
      rw [conv3_eq, lap3_eq (u t) (slice_contDiff hns.smooth_u ht), grad3_eq,
        extForce_eq f ht] at hm
      exact hm
    div_free := by
      intro x t ht
      show NavierStokes.Comparator.divergence (u t) x = 0
      rw [← div3_eq (u t) x ((slice_contDiff hns.smooth_u ht).differentiable (by simp) x)]
      exact hns.incompressible t ht x
    initial_condition := fun x => hns.initial x
    velocity_smooth := contDiffOn_swap hns.smooth_u
    pressure_smooth := contDiffOn_swap hns.smooth_p }

/-- Toda solução ATK espacialmente periódica é solução periódica no sentido deles. -/
theorem periodic_of_classical {ν : ℝ} {u0 : R3 → R3} {f : R3 → ℝ → R3} {u : ℝ → R3 → R3}
    {p : ℝ → R3 → ℝ} (hns : ATK.Exact.NSClassical ν u0 (extForce f) u p)
    (hper : ATK.Exact.SpacePeriodic u p) :
    NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u0 f
      (fun x t => u t x) (fun x t => p t x) :=
  { toNavierStokesExistenceAndSmoothness := base_of_classical hns
    isOnePeriodic_velocity := fun t ht x i => (hper t ht x i).1
    isOnePeriodic_pressure := fun t ht x i => (hper t ht x i).2 }

/-- **Ponte (D).** O enunciado (D) da OpenAI implica o alvo oficial ATK `ClayD`. -/
theorem clayD_of_fc (h : FCBreakdownPeriodic) : ATK.Exact.ClayD := by
  intro ν hν
  obtain ⟨u0, f, hu0, hf, hno⟩ := h ν hν
  refine ⟨u0, extForce f, hu0.smooth, fun x => ?_, fun x j => hu0.isOnePeriodic x j,
    smoothForce_ext hf.smooth, periodicForce_ext hf, ?_⟩
  · rw [div3_eq u0 x ((hu0.smooth.differentiable (by simp)) x)]
    exact hu0.div_free x
  · rintro ⟨u, p, hns, hper⟩
    exact hno ⟨fun x t => u t x, fun x t => p t x, periodic_of_classical hns hper⟩

end ATK.NSBridgeD

end

#print axioms ATK.NSBridgeD.extForce_eq
#print axioms ATK.NSBridgeD.smoothForce_ext
#print axioms ATK.NSBridgeD.periodicForce_ext
#print axioms ATK.NSBridgeD.base_of_classical
#print axioms ATK.NSBridgeD.periodic_of_classical
#print axioms ATK.NSBridgeD.clayD_of_fc
