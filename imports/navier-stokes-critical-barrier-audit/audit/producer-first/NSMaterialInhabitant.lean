/-!
NS material inhabitant interface.

This file is compiled by concatenating it after ProducerFirst.lean and
SignedGainCore.lean. It adds no axiom, sorry, admit, or hidden inhabitant.

It deliberately does NOT claim that the material inhabitant exists.  The
remaining mathematical obligation is exactly the genuine 3D Navier--Stokes
producer ActualNSToSignedGainCore.
-/

noncomputable section

namespace NSProducerFirst

/-- Canonical name for the unique remaining material inhabitant. -/
def NSMaterialInhabitant
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Type :=
  ActualNSToSignedGainCore State ActualNS ν data

/-- A genuine material inhabitant immediately reconstructs the previously
kernel-checked full signed-gain producer. -/
def materialInhabitant_to_signedGain
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (hν : 0 ≤ ν)
    (P : NSMaterialInhabitant State ActualNS ν data) :
    ActualNSToSignedGain State ActualNS ν data :=
  actualNSToSignedGain_of_core hν P

/-- Pointwise extraction of the full signed-gain certificate from the material
inhabitant. -/
theorem materialInhabitant_certificate
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (hν : 0 ≤ ν)
    (P : NSMaterialInhabitant State ActualNS ν data)
    (u : State)
    (hu : ActualNS u) :
    SignedGainCertificate ν (data u) :=
  materialInhabitant_to_signedGain hν P u hu

/-- Once the exact enstrophy balance is supplied by the genuine flow, the
material inhabitant yields the certified differential inequality with no
additional analytic oracle. -/
theorem materialInhabitant_implies_differential
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (hν : 0 ≤ ν)
    (P : NSMaterialInhabitant State ActualNS ν data)
    (balance :
      ∀ u : State, ActualNS u →
        ∀ t,
          (1 / 2 : ℝ) * deriv (data u).y t + ν * (data u).z t =
            (data u).stretch t) :
    ∀ u : State, ActualNS u →
      ∀ t,
        deriv (data u).y t +
            2 * (1 - (materialInhabitant_certificate hν P u ‹ActualNS u›).theta) *
              ν * (data u).z t
          ≤
            2 * (materialInhabitant_certificate hν P u ‹ActualNS u›).C *
              ((data u).y t)^2 := by
  intro u hu
  exact signedGain_implies_differential
    ν (data u) (balance u hu) (materialInhabitant_certificate hν P u hu)

/-- Positive viscosity plus the material inhabitant gives a strictly positive
dissipative margin for every genuine NS state. -/
theorem materialInhabitant_dissipation_margin_pos
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (hν : 0 < ν)
    (P : NSMaterialInhabitant State ActualNS ν data) :
    ∀ u : State, ActualNS u →
      0 <
        2 * (1 - (P u ‹ActualNS u›).theta) * ν := by
  intro u hu
  have hcore := P u hu
  have hmargin : 0 < 1 - hcore.theta := sub_pos.mpr hcore.htheta1
  positivity

/-- Exact fail-closed statement: the final material step is equivalent to
providing the canonical producer itself.  This theorem prevents an arbitrary
`Inhabited` instance from being mistaken for mathematical content. -/
theorem materialInhabitant_iff_terminalProducer
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData} :
    Nonempty (NSMaterialInhabitant State ActualNS ν data) ↔
      Nonempty (ActualNSToSignedGainCore State ActualNS ν data) := by
  rfl

end NSProducerFirst
