import G1_KAdmissible_to_SignedDepletion

noncomputable section

namespace MillenniumAudit.NS003

open MillenniumAudit.G1KAdmissible

/--
Concrete G1 theorem on the existing Navier--Stokes audit structures.

Analytic bulk absorption + exceptional-tail control + one strict shared budget
produce a positive depletion delta. Combined with the exact enstrophy balance,
this yields the strict dissipative differential inequality

  y'(t) + 2 delta nu z(t) <= 0.

No amplitude-invariant fixed-delta hypothesis is used.
No axiom, sorry, or admit is introduced here.
-/
theorem strict_signed_depletion_to_genuine_G1
    (ν cBulk δTail : ℝ)
    (hν : 0 ≤ ν)
    (d : EnstrophyData)
    (s : StretchSplit d)
    (hBalance : EnstrophyBalance ν d)
    (hBulk : BulkAbsorption ν cBulk d s)
    (hTail : ExceptionalTailControl ν δTail d s)
    (hBudget : SubcriticalBudget cBulk δTail) :
    ∃ δ : ℝ,
      0 < δ ∧
      δ ≤ 1 ∧
      (∀ t, d.stretch t ≤ (1 - δ) * ν * d.z t) ∧
      (∀ t, d.yDerivative t + 2 * δ * ν * d.z t ≤ 0) := by
  rcases G1bc_bulk_tail_to_signed_depletion
      ν cBulk δTail hν d s hBulk hTail hBudget with
    ⟨θ, hθ0, hθ1, hstretch⟩
  let δ : ℝ := 1 - θ
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    linarith
  have hdep : ∀ t, d.stretch t ≤ (1 - δ) * ν * d.z t := by
    intro t
    dsimp [δ]
    simpa using hstretch t
  refine ⟨δ, hδpos, hδle, hdep, ?_⟩
  intro t
  have hb := hBalance.balance t
  have hs := hdep t
  linarith

/--
The exact G1 implication isolated from the construction step:
any positive signed depletion coefficient plus enstrophy balance yields
the strict dissipative inequality.
-/
theorem signed_depletion_balance_implies_G1
    (ν δ : ℝ)
    (d : EnstrophyData)
    (hδ : 0 < δ)
    (hBalance : EnstrophyBalance ν d)
    (hDepletion : ∀ t, d.stretch t ≤ (1 - δ) * ν * d.z t) :
    ∀ t, d.yDerivative t + 2 * δ * ν * d.z t ≤ 0 := by
  intro t
  have hb := hBalance.balance t
  have hs := hDepletion t
  linarith

end MillenniumAudit.NS003
