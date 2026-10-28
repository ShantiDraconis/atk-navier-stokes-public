import Mathlib

namespace NSNearFieldAudit

structure TestedPDEIdentity where
  rhoStar : ℝ
  radius : ℝ
  nearTerm : ℝ
  C : ℝ
  rho_pos : 0 < rhoStar
  radius_pos : 0 < radius
  C_nonneg : 0 ≤ constant
  exact_test_identity : Prop
  diffusion_term_present : Prop

def ImprovedNearFieldBound (I : TestedPDEIdentity) : Prop :=
  I.nearTerm ≤
    I.C /
      (Real.sqrt I.rhoStar * (I.radius ^ 2) * Real.sqrt I.radius)

def NearFieldTarget : Prop :=
  ∀ I : TestedPDEIdentity,
    I.exact_test_identity →
    I.diffusion_term_present →
    ImprovedNearFieldBound I

def ScientificStatus : String := "OPEN_BRIDGE_NEAR_FIELD"

def ForbiddenPremises : List String :=
  [ "hDynamic"
  , "Holder_1_2"
  , "CriticalL3Bound"
  , "UniformEnstrophy"
  , "target_regular_geometry"
  ]

theorem improved_target_is_explicit (I : TestedPDEIdentity) :
    ImprovedNearFieldBound I ↔
      I.nearTerm ≤
        I.C /
          (Real.sqrt I.rhoStar * (I.radius ^ 2) * Real.sqrt I.radius) :=
  Iff.rfl

#print axioms NSNearFieldAudit.improved_target_is_explicit

end NSNearFieldAudit
