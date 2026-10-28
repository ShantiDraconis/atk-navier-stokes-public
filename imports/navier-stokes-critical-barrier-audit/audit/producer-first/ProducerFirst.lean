import Mathlib

noncomputable section

namespace NSProducerFirst

/-- Scalar enstrophy bookkeeping.  In the intended PDE interpretation,
    y = ||omega||_2^2, z = ||grad omega||_2^2, and stretch = integral omega.S.omega. -/
structure EnstrophyData where
  y : ℝ → ℝ
  z : ℝ → ℝ
  stretch : ℝ → ℝ
  hy : ∀ t, 0 ≤ y t
  hz : ∀ t, 0 ≤ z t

/-- The exact producer certificate still missing from genuine 3D NS dynamics.
    Its residual is energy-compatible: C*y^2, equivalently a(t)*y(t)
    with a(t)=C*y(t). -/
structure SignedGainCertificate (ν : ℝ) (d : EnstrophyData) where
  theta : ℝ
  C : ℝ
  htheta0 : 0 ≤ theta
  htheta1 : theta < 1
  hC : 0 ≤ C
  stretching :
    ∀ t, d.stretch t ≤ theta * ν * d.z t + C * (d.y t)^2

/-- Downstream flexible stretching target. -/
structure FlexibleStretchingBound (ν : ℝ) (d : EnstrophyData) where
  theta : ℝ
  a : ℝ → ℝ
  htheta0 : 0 ≤ theta
  htheta1 : theta < 1
  ha : ∀ t, 0 ≤ a t
  stretching :
    ∀ t, d.stretch t ≤ theta * ν * d.z t + a t * d.y t

/-- Minimal exact producer for the lower-order coefficient. -/
def producerA (C : ℝ) (d : EnstrophyData) (t : ℝ) : ℝ :=
  C * d.y t

theorem producerA_nonnegative
    (C : ℝ) (d : EnstrophyData) (hC : 0 ≤ C) :
    ∀ t, 0 ≤ producerA C d t := by
  intro t
  exact mul_nonneg hC (d.hy t)

theorem producerA_residual_exact
    (C : ℝ) (d : EnstrophyData) (t : ℝ) :
    producerA C d t * d.y t = C * (d.y t)^2 := by
  simp [producerA, pow_two, mul_assoc]

/-- Once the signed energy-compatible gain is genuinely produced,
    the FlexibleStretchingBound inhabitant is constructed with no new oracle. -/
def signedGain_to_flexible
    (ν : ℝ) (d : EnstrophyData)
    (h : SignedGainCertificate ν d) :
    FlexibleStretchingBound ν d where
  theta := h.theta
  a := producerA h.C d
  htheta0 := h.htheta0
  htheta1 := h.htheta1
  ha := producerA_nonnegative h.C d h.hC
  stretching := by
    intro t
    simpa [producerA, pow_two, mul_assoc] using h.stretching t

/-- Direct differential consequence of the exact enstrophy balance and the
signed-gain certificate.  No geometric/CZ input is introduced here: all open
PDE content remains inside `SignedGainCertificate`.

The identity
  (1/2) y' + nu z = stretch
combined with
  stretch <= theta nu z + C y^2
gives
  y' + 2(1-theta) nu z <= 2 C y^2.
-/
theorem signedGain_implies_differential
    (ν : ℝ) (d : EnstrophyData)
    (hbalance : ∀ t,
      (1 / 2 : ℝ) * deriv d.y t + ν * d.z t = d.stretch t)
    (h : SignedGainCertificate ν d) :
    ∀ t,
      deriv d.y t + 2 * (1 - h.theta) * ν * d.z t
        ≤ 2 * h.C * (d.y t)^2 := by
  intro t
  have hb := hbalance t
  have hs := h.stretching t
  nlinarith

/-- The dissipative coefficient in the preceding inequality is genuinely
strictly positive whenever viscosity is positive. -/
theorem signedGain_dissipation_margin_pos
    (ν : ℝ) (hν : 0 < ν)
    (d : EnstrophyData)
    (h : SignedGainCertificate ν d) :
    0 < 2 * (1 - h.theta) * ν := by
  have hmargin : 0 < 1 - h.theta := sub_pos.mpr h.htheta1
  positivity

/-- Scalar summary of the independent Leray energy budget.
    totalY represents integral y(t) dt. -/
structure EnergyBudget where
  ν : ℝ
  E0 : ℝ
  totalY : ℝ
  hν : 0 < ν
  hE0 : 0 ≤ E0
  htotalY : 0 ≤ totalY
  budget : totalY ≤ E0 / (2 * ν)

/-- With a(t)=C*y(t), its total mass is C*totalY and is therefore
    controlled by the already available energy budget. -/
theorem producerA_total_budget
    (C : ℝ) (hC : 0 ≤ C) (e : EnergyBudget) :
    C * e.totalY ≤ C * (e.E0 / (2 * e.ν)) :=
  mul_le_mul_of_nonneg_left e.budget hC

/-- Standard unsigned Young bookkeeping has coefficient proportional to y^2,
    hence residual proportional to y^3. -/
def standardUnsignedCoefficient (C y : ℝ) : ℝ := C * y^2

theorem standard_unsigned_residual_is_cubic (C y : ℝ) :
    standardUnsignedCoefficient C y * y = C * y^3 := by
  unfold standardUnsignedCoefficient
  ring

/-- The energy-compatible producer has coefficient proportional to y,
    hence residual proportional to y^2. -/
def energyCompatibleCoefficient (C y : ℝ) : ℝ := C * y

theorem energy_compatible_residual_is_quadratic (C y : ℝ) :
    energyCompatibleCoefficient C y * y = C * y^2 := by
  unfold energyCompatibleCoefficient
  ring

/-- Exact terminal OPEN_MATH type.  No inhabitant is asserted here.
    A proof must construct this map from the genuine Navier-Stokes solution
    class, rather than assume it through an interface. -/
def ActualNSToSignedGain
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Type :=
  (u : State) → ActualNS u → SignedGainCertificate ν (data u)


/-- A deliberately impossible scalar profile: positive stretching with zero
enstrophy and zero dissipation. It is not claimed to arise from Navier--Stokes;
it is a type-level nontriviality test for the terminal producer. -/
def impossibleSignedGainData : EnstrophyData where
  y := fun _ => 0
  z := fun _ => 0
  stretch := fun _ => 1
  hy := by intro t; norm_num
  hz := by intro t; norm_num

/-- Nontriviality firewall: the producer target cannot be manufactured for
arbitrary EnstrophyData by choosing zero/default fields. -/
theorem signedGainCertificate_not_trivially_inhabited :
    ¬ Nonempty (SignedGainCertificate 1 impossibleSignedGainData) := by
  rintro ⟨h⟩
  have hs := h.stretching 0
  norm_num [impossibleSignedGainData] at hs

end NSProducerFirst
