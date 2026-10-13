import Mathlib
import ATK.Exact
import ATK.Closure

/-!
# ATK — Linha de explosão para Navier–Stokes

No NS a explosão é literal (blow-up). Formato de cada linha de explosão do programa:

* **testemunha de explosão** — um objeto cuja existência fecha a questão;
* **refutação** — `testemunha → ¬ alvo` (ou `→ alvo`, quando o alvo é a própria explosão);
* **dicotomia** — `alvo ↔ IsEmpty testemunha`: fechar pelo lado regular é provar que a
  testemunha não existe; fechar pelo lado explosivo é exibir uma.

Estado em 13/10/2026:
* (C) e (D) — explosão COM força: **realizadas** (prova externa; `NSBridge`, `NSBridgeD`);
* (A) e (B) — explosão SEM força: testemunhas `UnforcedBlowupR3`, `UnforcedBlowupTorus` abaixo;
  nenhuma conhecida. Uma testemunha em ℝ³ refutaria (A) e daria (C) de novo, sem força
  (`explosion_gives_C`).
-/

noncomputable section

namespace ATK.NSExplosion

open ATK.Exact
open scoped ContDiff

/-- Testemunha de explosão sem força em `ℝ³` (refuta (A)). -/
structure UnforcedBlowupR3 where
  ν : ℝ
  hν : 0 < ν
  u0 : R3 → R3
  smooth : ContDiff ℝ ∞ u0
  divFree : ∀ x, div3 u0 x = 0
  decay : RapidDecay u0
  noSolution : ¬ ∃ u p, NSClassical ν u0 (fun _ _ => 0) u p ∧ BoundedEnergy u

theorem explosion_refutes_A (w : UnforcedBlowupR3) : ¬ ClayA := fun h =>
  w.noSolution (h w.ν w.hν w.u0 w.smooth w.divFree w.decay)

/-- Dicotomia (A): regularidade global ⇔ não existe explosão sem força. -/
theorem clayA_iff_no_explosion : ClayA ↔ IsEmpty UnforcedBlowupR3 := by
  constructor
  · intro h
    exact ⟨fun w => explosion_refutes_A w h⟩
  · intro h ν hν u0 hs hd hr
    by_contra hno
    exact h.1 ⟨ν, hν, u0, hs, hd, hr, hno⟩

/-- Uma explosão sem força em ℝ³ também prova (C) (força nula + reescala). -/
theorem explosion_gives_C (w : UnforcedBlowupR3) : ClayC :=
  ATK.Closure.clayA_or_clayC.resolve_left (explosion_refutes_A w)

/-- Testemunha de explosão sem força no toro (refuta (B)). -/
structure UnforcedBlowupTorus where
  ν : ℝ
  hν : 0 < ν
  u0 : R3 → R3
  smooth : ContDiff ℝ ∞ u0
  divFree : ∀ x, div3 u0 x = 0
  periodic : PeriodicData u0
  noSolution : ¬ ∃ u p, NSClassical ν u0 (fun _ _ => 0) u p ∧ SpacePeriodic u p

theorem explosion_refutes_B (w : UnforcedBlowupTorus) : ¬ ClayB := fun h =>
  w.noSolution (h w.ν w.hν w.u0 w.smooth w.divFree w.periodic)

/-- Dicotomia (B). -/
theorem clayB_iff_no_explosion : ClayB ↔ IsEmpty UnforcedBlowupTorus := by
  constructor
  · intro h
    exact ⟨fun w => explosion_refutes_B w h⟩
  · intro h ν hν u0 hs hd hp
    by_contra hno
    exact h.1 ⟨ν, hν, u0, hs, hd, hp, hno⟩

end ATK.NSExplosion

end

#print axioms ATK.NSExplosion.explosion_refutes_A
#print axioms ATK.NSExplosion.clayA_iff_no_explosion
#print axioms ATK.NSExplosion.explosion_gives_C
#print axioms ATK.NSExplosion.explosion_refutes_B
#print axioms ATK.NSExplosion.clayB_iff_no_explosion
