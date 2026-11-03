import Mathlib

namespace NSPositiveHabitantCore

universe u v

section

variable {InitialData : Type u}
variable {Trajectory : Type v}

variable (Admissible : InitialData → Prop)
variable (IsMaximalSmoothNS : InitialData → Trajectory → Prop)
variable (CriticalL3Finite : Trajectory → Prop)
variable (GlobalSmooth : InitialData → Trajectory → Prop)

def UniformCriticalL3Producer : Prop :=
  ∀ u0, Admissible u0 →
    ∀ u, IsMaximalSmoothNS u0 u →
      CriticalL3Finite u

def EndpointCertificate : Prop :=
  ∀ u0, Admissible u0 →
    ∀ u, IsMaximalSmoothNS u0 u →
      CriticalL3Finite u →
      GlobalSmooth u0 u

theorem producer_enables_global
    (hProducer : UniformCriticalL3Producer
      Admissible IsMaximalSmoothNS CriticalL3Finite)
    (hEndpoint : EndpointCertificate
      Admissible IsMaximalSmoothNS CriticalL3Finite GlobalSmooth) :
    ∀ u0, Admissible u0 →
      ∀ u, IsMaximalSmoothNS u0 u →
        GlobalSmooth u0 u := by
  intro u0 hu0 u hNS
  exact hEndpoint u0 hu0 u hNS (hProducer u0 hu0 u hNS)

def OpenMathProducer : Prop :=
  UniformCriticalL3Producer
    Admissible IsMaximalSmoothNS CriticalL3Finite

theorem open_math_exact :
    OpenMathProducer Admissible IsMaximalSmoothNS CriticalL3Finite ↔
    UniformCriticalL3Producer
      Admissible IsMaximalSmoothNS CriticalL3Finite := by
  rfl

#print axioms producer_enables_global
#print axioms open_math_exact

end

end NSPositiveHabitantCore
