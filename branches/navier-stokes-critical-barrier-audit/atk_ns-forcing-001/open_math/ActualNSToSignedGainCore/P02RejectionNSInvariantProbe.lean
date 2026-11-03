import Mathlib

/-!
T7-NS-REJECTION / scaling invariant probe.

Negative guard for the Navier--Stokes forcing lane.

The purpose of this file is deliberately limited: the algebraic scaling laws
alone cannot promote a nonzero blow-up defect to zero.  The material endpoint
must therefore come from an additional analytic/coercive estimate rather than
from the scale-group structure itself.

No claim of global regularity is made here.
-/

noncomputable section

namespace NSProducerFirst.P02RejectionNSInvariantProbe

/-- Positive scaling parameters.  Excluding zero is essential: Leray scaling
forms a multiplicative group only for nonzero (here positive) parameters. -/
abbrev Scale := { lam : ℝ // 0 < lam }

/-- Minimal algebraic model seen by the rejection probe. -/
structure ScaleModel where
  Point : Type
  scale : Scale → Point → Point
  defect : Point → ℝ
  scale_one : ∀ x, scale ⟨1, by norm_num⟩ x = x
  scale_mul :
    ∀ (lam mu : Scale) (x : Point),
      scale ⟨lam.1 * mu.1, mul_pos lam.2 mu.2⟩ x =
        scale lam (scale mu x)
  defect_scale :
    ∀ (lam : Scale) (x : Point),
      defect (scale lam x) = lam.1 ^ 2 * defect x

/-- Reciprocal positive scale. -/
def invScale (lam : Scale) : Scale :=
  ⟨lam.1⁻¹, inv_pos.mpr lam.2⟩

@[simp] theorem invScale_val (lam : Scale) :
    (invScale lam).1 = lam.1⁻¹ := rfl

/-- Q1/Q2/Q3 consequence: scaling by lam and then by lam⁻¹ returns the
original point.  This is a group inverse, not idempotence. -/
theorem scale_inverse
    (M : ScaleModel) (lam : Scale) (x : M.Point) :
    M.scale (invScale lam) (M.scale lam x) = x := by
  rw [← M.scale_mul]
  have hne : lam.1 ≠ 0 := ne_of_gt lam.2
  have hprod : lam.1⁻¹ * lam.1 = 1 := inv_mul_cancel₀ hne
  have hs :
      (⟨(invScale lam).1 * lam.1,
          mul_pos (invScale lam).2 lam.2⟩ : Scale) =
        ⟨1, by norm_num⟩ := by
    apply Subtype.ext
    simpa [invScale] using hprod
  rw [hs, M.scale_one]

/-- Q5: a strictly positive defect stays strictly positive along every
positive scaling orbit. -/
theorem positive_defect_preserved
    (M : ScaleModel) (x : M.Point)
    (hx : 0 < M.defect x) (lam : Scale) :
    0 < M.defect (M.scale lam x) := by
  rw [M.defect_scale]
  exact mul_pos (sq_pos_of_pos lam.2) hx

/-- The weaker nonzero form needed by the rejection guard. -/
theorem nonzero_defect_preserved
    (M : ScaleModel) (x : M.Point)
    (hx : M.defect x ≠ 0) (lam : Scale) :
    M.defect (M.scale lam x) ≠ 0 := by
  rw [M.defect_scale]
  exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt lam.2)) hx

/-- Zero defect is also preserved by scaling.  Hence zero and nonzero defects
cannot be connected by an invertible scale action satisfying the covariance
law. -/
theorem zero_defect_preserved
    (M : ScaleModel) (x : M.Point)
    (hx : M.defect x = 0) (lam : Scale) :
    M.defect (M.scale lam x) = 0 := by
  rw [M.defect_scale, hx, mul_zero]

/-- Q8: explicit countermodel.  It satisfies the group-style scale law and
the quadratic defect covariance while still containing positive defect. -/
def toyScaleModel : ScaleModel where
  Point := ℝ
  scale := fun lam x => lam.1 ^ 2 * x
  defect := id
  scale_one := by
    intro x
    simp
  scale_mul := by
    intro lam mu x
    dsimp
    ring
  defect_scale := by
    intro lam x
    rfl

theorem toy_has_positive_defect :
    0 < toyScaleModel.defect (show toyScaleModel.Point from (1 : ℝ)) := by
  change 0 < (1 : ℝ)
  norm_num

/-- Q8/Q9: the scaling axioms are jointly satisfiable with nonzero defect.
Therefore they do not entail defect collapse. -/
theorem scaling_axioms_do_not_force_defect_zero :
    ∃ (M : ScaleModel) (x : M.Point), M.defect x ≠ 0 := by
  refine ⟨toyScaleModel, (show toyScaleModel.Point from (1 : ℝ)), ?_⟩
  change (1 : ℝ) ≠ 0
  norm_num

/-- Orbit-collapse formulation of the diagonal obstruction:
for a point with nonzero defect there is no positive scale at which the
defect becomes zero. -/
theorem no_scale_orbit_collapse
    (M : ScaleModel) (x : M.Point)
    (hx : M.defect x ≠ 0) :
    ¬ ∃ lam : Scale, M.defect (M.scale lam x) = 0 := by
  rintro ⟨lam, hzero⟩
  exact (nonzero_defect_preserved M x hx lam) hzero

/-- Q10 guard: any proposed theorem asserting that every point can be scaled
onto defect zero is incompatible with the scale covariance laws whenever the
model has one nonzero-defect point. -/
theorem universal_scale_collapse_forbidden
    (M : ScaleModel)
    (hx : ∃ x : M.Point, M.defect x ≠ 0) :
    ¬ (∀ x : M.Point, ∃ lam : Scale, M.defect (M.scale lam x) = 0) := by
  intro hcollapse
  obtain ⟨x, hx0⟩ := hx
  obtain ⟨lam, hzero⟩ := hcollapse x
  exact (nonzero_defect_preserved M x hx0 lam) hzero


/-- Terminal opposition probe: over the real field, a point fixed by negation
is exactly the zero point. Thus an equation of the form x = -x is a zero-state
collapse, not a proof of a nontrivial endpoint. -/
theorem real_eq_neg_self_iff_zero (x : ℝ) :
    x = -x ↔ x = 0 := by
  constructor
  · intro h
    linarith
  · intro h
    simp [h]

/-- There is no universal real opposition fixed-point law. -/
theorem not_every_real_eq_neg_self :
    ¬ (∀ x : ℝ, x = -x) := by
  intro h
  have h1 := h 1
  norm_num at h1

/-- Formal boundary exposed by the probe.  This is intentionally only a
predicate name: inhabiting it for genuine 3D Navier--Stokes dynamics remains
the material analytic obligation. -/
def AdditionalAnalyticCollapse (M : ScaleModel) : Prop :=
  ∀ x : M.Point, M.defect x = 0

/-- The toy model refutes any attempt to manufacture the analytic endpoint
from the scale structure alone. -/
theorem toy_rejects_analytic_collapse :
    ¬ AdditionalAnalyticCollapse toyScaleModel := by
  intro h
  have h1 := h (show toyScaleModel.Point from (1 : ℝ))
  change (1 : ℝ) = 0 at h1
  norm_num at h1

end NSProducerFirst.P02RejectionNSInvariantProbe
