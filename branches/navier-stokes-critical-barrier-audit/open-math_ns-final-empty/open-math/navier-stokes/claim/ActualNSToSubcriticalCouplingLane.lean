import Mathlib

namespace NSActualNSToSubcriticalCoupling

structure NSEData where
  nu : ℝ
  hnu : 0 < nu

def ActualNS {State : Type}
    (NSPredicate : NSEData → State → Prop)
    (D : NSEData) (u : State) : Prop :=
  NSPredicate D u

structure DynamicQBound {State : Type} (D : NSEData) (u : State) where
  q : ℝ → ℝ
  hq : ∀ t, 0 ≤ q t
  uniformBound : ℝ
  hUniformBound : 0 ≤ uniformBound
  q_le : ∀ t, q t ≤ uniformBound

structure KernelWeightedCoherence {State : Type} (D : NSEData) (u : State) where
  coefficient : ℝ → ℝ
  hcoefficient : ∀ t, 0 ≤ coefficient t
  holds : Prop

structure ExceptionalTailControl {State : Type} (D : NSEData) (u : State) where
  tailWeight : ℝ → ℝ
  htailWeight : ∀ t, 0 ≤ tailWeight t
  tailBound : ℝ
  htailBound : 0 ≤ tailBound
  tail_le : ∀ t, tailWeight t ≤ tailBound

structure LowFrequencyControl {State : Type} (D : NSEData) (u : State) where
  lowWeight : ℝ → ℝ
  hlowWeight : ∀ t, 0 ≤ lowWeight t
  lowBound : ℝ
  hlowBound : 0 ≤ lowBound
  low_le : ∀ t, lowWeight t ≤ lowBound

structure LPQuantities {State : Type} (D : NSEData) (u : State) where
  lowWeight : ℝ → ℝ
  highWeight : ℝ → ℝ
  lowWeight_nonneg : ∀ t, 0 ≤ lowWeight t
  highWeight_nonneg : ∀ t, 0 ≤ highWeight t

def SubcriticalCoupling
    {State : Type} {D : NSEData} {u : State}
    (L : LPQuantities D u) : Prop :=
  ∃ cLow cTail : ℝ,
    0 ≤ cLow ∧
    0 ≤ cTail ∧
    (∀ t, L.lowWeight t ≤ cLow) ∧
    (∀ t, L.highWeight t ≤ cTail) ∧
    cLow + cTail < 1

structure ActualNSToDynamicQ
    (State : Type)
    (NSPredicate : NSEData → State → Prop)
    (D : NSEData) where
  bridge : ∀ u : State, ActualNS NSPredicate D u → DynamicQBound D u

structure DynamicQToKernel
    (State : Type) (D : NSEData) where
  bridge : ∀ u : State, DynamicQBound D u → KernelWeightedCoherence D u

structure KernelToTail
    (State : Type) (D : NSEData) where
  bridge : ∀ u : State, KernelWeightedCoherence D u → ExceptionalTailControl D u

structure ActualNSToLowFrequency
    (State : Type)
    (NSPredicate : NSEData → State → Prop)
    (D : NSEData) where
  bridge : ∀ u : State, ActualNS NSPredicate D u → LowFrequencyControl D u

structure StrictCombinedBudget
    (State : Type)
    (NSPredicate : NSEData → State → Prop)
    (D : NSEData) where
  bridge :
    ∀ u : State,
      ActualNS NSPredicate D u →
      LowFrequencyControl D u →
      ExceptionalTailControl D u →
      Prop
  realizes :
    ∀ u : State, ∀ hu : ActualNS NSPredicate D u,
      ∀ low : LowFrequencyControl D u,
      ∀ tail : ExceptionalTailControl D u,
      bridge u hu low tail →
      low.lowBound + tail.tailBound < 1

def assembleLP
    {State : Type} {D : NSEData} {u : State}
    (low : LowFrequencyControl D u)
    (tail : ExceptionalTailControl D u) :
    LPQuantities D u where
  lowWeight := low.lowWeight
  highWeight := tail.tailWeight
  lowWeight_nonneg := low.hlowWeight
  highWeight_nonneg := tail.htailWeight

theorem subcriticalCoupling_of_controls
    {State : Type} {D : NSEData} {u : State}
    (low : LowFrequencyControl D u)
    (tail : ExceptionalTailControl D u)
    (hstrict : low.lowBound + tail.tailBound < 1) :
    SubcriticalCoupling (assembleLP low tail) := by
  refine ⟨low.lowBound, tail.tailBound,
    low.hlowBound, tail.htailBound, ?_, ?_, hstrict⟩
  · intro t
    exact low.low_le t
  · intro t
    exact tail.tail_le t

theorem actualNS_to_subcriticalCoupling
    {State : Type}
    {NSPredicate : NSEData → State → Prop}
    (D : NSEData)
    (nsToQ : ActualNSToDynamicQ State NSPredicate D)
    (qToKernel : DynamicQToKernel State D)
    (kernelToTail : KernelToTail State D)
    (nsToLow : ActualNSToLowFrequency State NSPredicate D)
    (strictBudget : StrictCombinedBudget State NSPredicate D)
    (strictEvidence :
      ∀ u : State, ∀ hu : ActualNS NSPredicate D u,
        strictBudget.bridge u hu
          (nsToLow.bridge u hu)
          (kernelToTail.bridge u (qToKernel.bridge u (nsToQ.bridge u hu)))) :
    ∀ u : State, ActualNS NSPredicate D u →
      ∃ L : LPQuantities D u, SubcriticalCoupling L := by
  intro u hu
  let low := nsToLow.bridge u hu
  let q := nsToQ.bridge u hu
  let kernel := qToKernel.bridge u q
  let tail := kernelToTail.bridge u kernel
  have hs : strictBudget.bridge u hu low tail := by
    simpa [low, q, kernel, tail] using strictEvidence u hu
  have hlt : low.lowBound + tail.tailBound < 1 :=
    strictBudget.realizes u hu low tail hs
  exact ⟨assembleLP low tail, subcriticalCoupling_of_controls low tail hlt⟩

def OpenFrontier
    (State : Type)
    (NSPredicate : NSEData → State → Prop)
    (D : NSEData) : Prop :=
  Nonempty (ActualNSToDynamicQ State NSPredicate D) ∧
  Nonempty (DynamicQToKernel State D) ∧
  Nonempty (KernelToTail State D) ∧
  Nonempty (ActualNSToLowFrequency State NSPredicate D) ∧
  Nonempty (StrictCombinedBudget State NSPredicate D)

#print axioms subcriticalCoupling_of_controls
#print axioms actualNS_to_subcriticalCoupling

end NSActualNSToSubcriticalCoupling
