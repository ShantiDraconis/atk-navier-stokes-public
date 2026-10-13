namespace NSMaterial
structure Closure (State : Type) where
  bulk tail remainder : State → Real
  nu z y : State → Real
  cBulk cTail C : Real
  budget : cBulk + cTail < 1
  cBulk_nonneg : 0 ≤ cBulk
  cTail_nonneg : 0 ≤ cTail
  C_nonneg : 0 ≤ C
  bulk_bound : ∀ s, bulk s ≤ cBulk * nu s * z s
  tail_bound : ∀ s, tail s ≤ cTail * nu s * z s
  remainder_bound : ∀ s, remainder s ≤ C * (y s)^2

def MaterialNSProducer (State : Type) : Prop := Nonempty (Closure State)
end NSMaterial
