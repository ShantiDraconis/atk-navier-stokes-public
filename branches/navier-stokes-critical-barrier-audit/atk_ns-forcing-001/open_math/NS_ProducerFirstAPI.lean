import Mathlib

noncomputable section

namespace NSProducerFirst

structure EnstrophyData where
  y : ℝ → ℝ
  z : ℝ → ℝ
  stretch : ℝ → ℝ
  hy : ∀ t, 0 ≤ y t
  hz : ∀ t, 0 ≤ z t

structure SignedGainCertificate (ν : ℝ) (d : EnstrophyData) where
  theta : ℝ
  C : ℝ
  htheta0 : 0 ≤ theta
  htheta1 : theta < 1
  hC : 0 ≤ C
  stretching :
    ∀ t, d.stretch t ≤ theta * ν * d.z t + C * (d.y t)^2

def ActualNSToSignedGain
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Type :=
  (u : State) → ActualNS u → SignedGainCertificate ν (data u)

end NSProducerFirst
