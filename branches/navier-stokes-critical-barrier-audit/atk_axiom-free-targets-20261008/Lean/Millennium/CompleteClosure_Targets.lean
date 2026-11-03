import Mathlib

noncomputable section
open Matrix

/-!
# Complete Closure Targets

B2.9 below is a finite-dimensional proved obstruction.
Every former `_TARGET` axiom is now a named `Prop` (`…_statement`); none is assumed.
-/

def C_Bernstein : ℝ := 4
def C_Sobolev_R3 : ℝ := 0.62
def C_error : ℝ := 2.48
def kappa (ν Λ : ℝ) : ℝ := ν * Λ^2 / 4
def cstar (ν : ℝ) : ℝ := ν / (4 * C_Sobolev_R3)

def S_divFree : Matrix (Fin 3) (Fin 3) ℝ := !![1,0,0; 0,-0.5,0; 0,0,-0.5]
def u1 : Fin 3 → ℝ := ![1,0,0]
def u2 : Fin 3 → ℝ := ![0,1,0]
def R_Lambda (norm2 : ℝ) : ℝ := (1/2 : ℝ) * norm2
def Pi_Lambda (S : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ) : ℝ := -(u ⬝ᵥ (S *ᵥ u))

theorem u1_dot_u1 : u1 ⬝ᵥ u1 = 1 := by
  simp [u1, Matrix.vec3_dotProduct]

theorem u2_dot_u2 : u2 ⬝ᵥ u2 = 1 := by
  simp [u2, Matrix.vec3_dotProduct]

theorem Pi_u1 : Pi_Lambda S_divFree u1 = -1 := by
  simp [Pi_Lambda, S_divFree, u1, Matrix.mulVec, Matrix.vec3_dotProduct,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply] <;> norm_num

theorem Pi_u2 : Pi_Lambda S_divFree u2 = 1 / 2 := by
  simp [Pi_Lambda, S_divFree, u2, Matrix.mulVec, Matrix.vec3_dotProduct,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply] <;> norm_num

theorem B2_9_R_equal :
    R_Lambda (u1 ⬝ᵥ u1) = R_Lambda (u2 ⬝ᵥ u2) := by
  rw [u1_dot_u1, u2_dot_u2]

theorem B2_9_Pi_different :
    Pi_Lambda S_divFree u1 ≠ Pi_Lambda S_divFree u2 := by
  rw [Pi_u1, Pi_u2]
  norm_num

/-!
## OPEN specifications (audit 2026-10-08)

The `_TARGET`s below were global `axiom`s.  `B2_8_TARGET` was *false*, so the old
file made every importing environment inconsistent.  Each target is now a named
`Prop` (`…_statement`) that nothing assumes:

* `B2_8_statement` is refuted (`B2_8_statement_false`): for `u = u1`, `Λ = 1`,
  `ν = 100` the flux is `-1` while the required lower bound is `11.26`;
* `B2_10_statement`, `RH_G8_statement`, `YM_G16_statement`, `PvsNP_G11_statement`,
  `BSD_statement`, `HODGE_statement` are vacuous (their conclusion is `True` or
  witnessed by the literal `1`); they are proved below to make that explicit.
  They carry no information about the corresponding problems.
-/

/-- Former `axiom B2_8_TARGET` (lower-bound convention). -/
def B2_8_statement : Prop :=
  ∀ Λ ν : ℝ, ∀ u : Fin 3 → ℝ,
  Λ ≥ 1 → ν > 0 →
  ∃ κ : ℝ, κ = kappa ν Λ ∧
    Pi_Lambda S_divFree u ≥
      κ * R_Lambda (u ⬝ᵥ u) - C_error * Λ⁻¹ * R_Lambda (u ⬝ᵥ u)

/-- The former axiom `B2_8_TARGET` is false. -/
theorem B2_8_statement_false : ¬ B2_8_statement := by
  intro h
  obtain ⟨κ, hκ, hineq⟩ := h 1 100 u1 (by norm_num) (by norm_num)
  rw [hκ, Pi_u1, u1_dot_u1] at hineq
  norm_num [R_Lambda, kappa, C_error] at hineq

/-- Former `axiom B2_10_TARGET` (conclusion `True`). -/
def B2_10_statement : Prop := ∀ Λ ν T : ℝ, ν * Λ^2 > kappa ν Λ → True
theorem B2_10_statement_vacuous : B2_10_statement := fun _ _ _ _ => trivial

/-- Former `axiom RH_G8_TARGET` (conclusion `True`). -/
def RH_G8_statement : Prop := ∀ (_ρ_model : ℂ) (r : ℝ), r = 0.01 → True
theorem RH_G8_statement_vacuous : RH_G8_statement := fun _ _ _ => trivial

/-- Former `axiom YM_G16_TARGET` (witnessed by the literal `1`). -/
def YM_G16_statement : Prop := ∀ (_G : Type), ∃ Δ : ℝ, Δ = 1 ∧ Δ > 0
theorem YM_G16_statement_vacuous : YM_G16_statement := fun _ => ⟨1, rfl, one_pos⟩

/-- Former `axiom PvsNP_G11_TARGET : True`, `BSD_TARGET : True`, `HODGE_TARGET : True`. -/
def PvsNP_G11_statement : Prop := True
def BSD_statement : Prop := True
def HODGE_statement : Prop := True
theorem PvsNP_G11_statement_vacuous : PvsNP_G11_statement := trivial
theorem BSD_statement_vacuous : BSD_statement := trivial
theorem HODGE_statement_vacuous : HODGE_statement := trivial

def Final_Residues : List (String × String) :=
  [("NS", "0 target — M3<inf"),
   ("RH", "empty target — Re=0.5"),
   ("PvsNP", "SAT not in P target"),
   ("YM", "Delta=1>0 target normalization")]
