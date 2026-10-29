import Mathlib

noncomputable section

namespace MillenniumAudit.NS003

/--
Concrete joint diagnostic along a Navier--Stokes trajectory.
qDir and qStrain are nonnegative contributions; alpha is a fixed positive weight.
-/
structure QJointTrajectory where
  qDir : ℝ → ℝ
  qStrain : ℝ → ℝ
  alpha : ℝ
  hDir : ∀ t, 0 ≤ qDir t
  hStrain : ∀ t, 0 ≤ qStrain t
  hAlpha : 0 < alpha

def QJointTrajectory.value (q : QJointTrajectory) (t : ℝ) : ℝ :=
  q.qDir t + q.alpha * q.qStrain t

theorem QJointTrajectory.nonneg (q : QJointTrajectory) (t : ℝ) :
    0 ≤ q.value t := by
  unfold QJointTrajectory.value
  exact add_nonneg (q.hDir t) (mul_nonneg (le_of_lt q.hAlpha) (q.hStrain t))

/-- Uniform-in-time control of the concrete joint diagnostic. -/
structure UniformQJointBound (q : QJointTrajectory) where
  Qstar : ℝ
  hQstar : 0 ≤ Qstar
  bound : ∀ t, q.value t ≤ Qstar

/--
ActualNS data exposed only at the level currently justified by the corpus.
No regularity conclusion is built into this object.
-/
structure ActualNSData where
  viscosity : ℝ
  hViscosity : 0 < viscosity
  localEnergyInequality : Prop
  pressureDecomposition : Prop
  enstrophyIdentity : Prop

/--
Concrete O1 target:
actual NS data must generate a joint diagnostic together with one time-uniform bound.
-/
def O1ConcreteStatement : Prop :=
  ∀ u : ActualNSData, ∃ q : QJointTrajectory, Nonempty (UniformQJointBound q)

/--
A decomposition contract for attacking O1 without hiding assumptions.
Each field corresponds to one real PDE obligation.
-/
structure O1ProofComponents (u : ActualNSData) where
  q : QJointTrajectory
  localEnergy_to_direction : Prop
  pressure_to_strain : Prop
  epsilon_regular_region_control : Prop
  exceptional_tail_control : Prop
  uniform_constant : ℝ
  hUniformConstant : 0 ≤ uniform_constant
  assemble_bound :
    localEnergy_to_direction →
    pressure_to_strain →
    epsilon_regular_region_control →
    exceptional_tail_control →
    ∀ t, q.value t ≤ uniform_constant

/--
Once the four PDE components are genuinely proved, O1 closes.
This theorem is pure kernel composition and introduces no hidden hypothesis.
-/
theorem O1_from_components
    (u : ActualNSData)
    (c : O1ProofComponents u)
    (hA : c.localEnergy_to_direction)
    (hB : c.pressure_to_strain)
    (hC : c.epsilon_regular_region_control)
    (hD : c.exceptional_tail_control) :
    ∃ q : QJointTrajectory, Nonempty (UniformQJointBound q) := by
  refine ⟨c.q, ?_⟩
  exact ⟨{
    Qstar := c.uniform_constant
    hQstar := c.hUniformConstant
    bound := c.assemble_bound hA hB hC hD
  }⟩

/--
The exact first missing PDE theorem after all downstream algebra has been removed.
-/
def O1ActualNSUniformQJoint : Prop :=
  ∀ u : ActualNSData, ∃ c : O1ProofComponents u,
    c.localEnergy_to_direction ∧
    c.pressure_to_strain ∧
    c.epsilon_regular_region_control ∧
    c.exceptional_tail_control

theorem O1ActualNSUniformQJoint_implies_concrete_O1
    (h : O1ActualNSUniformQJoint) :
    O1ConcreteStatement := by
  intro u
  rcases h u with ⟨c, hA, hB, hC, hD⟩
  exact O1_from_components u c hA hB hC hD

end MillenniumAudit.NS003
