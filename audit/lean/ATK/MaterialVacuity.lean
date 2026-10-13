import Mathlib

/-!
# Auditoria de vacuidade — `NSMaterial.Closure` (`imports/Material/Closure.lean`)

Cópia da estrutura (namespace trocado). **Achado de compilação:** o original não compila em
Lean 4 — `bulk tail remainder : State → Real` sem parênteses declara UM campo `bulk` com
parâmetros `tail remainder` (sintaxe de campo simples), e os campos `tail`, `remainder`, `z`, `y`
deixam de existir (erro "Function expected"; verificado no CI ao compilar a cópia literal). Abaixo
está a intenção evidente, com os campos múltiplos entre parênteses. Resultado certificado pelo
kernel:

* `producer_trivial`: o "fechamento material" existe para QUALQUER tipo de estado, com todas as
  funções nulas;
* `producer_any_terms`: mais forte — para QUAISQUER termos `bulk`, `tail`, `remainder` dados, as
  cotas são satisfeitas escolhendo `nu`, `z`, `y` convenientes.

Motivo: `nu`, `z`, `y` são campos livres, não a viscosidade e as normas de uma solução de
Navier–Stokes. O orçamento `cBulk + cTail < 1` não restringe nada enquanto eles forem livres.
Estado: **CONDICIONAL**. Correção: `nu` = viscosidade fixa (parâmetro), `y` = enstrofia,
`z = ‖∇ω‖²` e `bulk + tail + remainder` = decomposição do estiramento `∫ ω·∇u·ω` de uma solução
suave genuína — e então as cotas passam a ser o conteúdo aberto.
-/

noncomputable section

namespace ATK.MaterialVacuity

structure Closure (State : Type) where
  (bulk tail remainder : State → Real)
  (nu z y : State → Real)
  (cBulk cTail C : Real)
  budget : cBulk + cTail < 1
  cBulk_nonneg : 0 ≤ cBulk
  cTail_nonneg : 0 ≤ cTail
  C_nonneg : 0 ≤ C
  bulk_bound : ∀ s, bulk s ≤ cBulk * nu s * z s
  tail_bound : ∀ s, tail s ≤ cTail * nu s * z s
  remainder_bound : ∀ s, remainder s ≤ C * (y s)^2

def MaterialNSProducer (State : Type) : Prop := Nonempty (Closure State)

/-- Vacuidade: todas as funções nulas habitam o "fechamento". -/
theorem producer_trivial (State : Type) : MaterialNSProducer State :=
  ⟨{ bulk := fun _ => 0, tail := fun _ => 0, remainder := fun _ => 0
     nu := fun _ => 0, z := fun _ => 0, y := fun _ => 0
     cBulk := 0, cTail := 0, C := 0
     budget := by norm_num
     cBulk_nonneg := le_rfl, cTail_nonneg := le_rfl, C_nonneg := le_rfl
     bulk_bound := fun _ => by simp
     tail_bound := fun _ => by simp
     remainder_bound := fun _ => by simp }⟩

/-- Vacuidade forte: QUAISQUER termos de estiramento `b`, `t`, `r` cabem no orçamento, porque
`nu`, `z`, `y` podem ser escolhidos depois deles. -/
theorem producer_any_terms (State : Type) (b t r : State → ℝ) :
    ∃ c : Closure State, c.bulk = b ∧ c.tail = t ∧ c.remainder = r :=
  ⟨{ bulk := b, tail := t, remainder := r
     nu := fun s => 4 * (|b s| + |t s|), z := fun _ => 1, y := fun s => Real.sqrt |r s|
     cBulk := 1 / 4, cTail := 1 / 4, C := 1
     budget := by norm_num
     cBulk_nonneg := by norm_num
     cTail_nonneg := by norm_num
     C_nonneg := by norm_num
     bulk_bound := fun s => by
       show b s ≤ 1 / 4 * (4 * (|b s| + |t s|)) * 1
       linarith [le_abs_self (b s), abs_nonneg (t s)]
     tail_bound := fun s => by
       show t s ≤ 1 / 4 * (4 * (|b s| + |t s|)) * 1
       linarith [le_abs_self (t s), abs_nonneg (b s)]
     remainder_bound := fun s => by
       show r s ≤ 1 * Real.sqrt |r s| ^ 2
       rw [Real.sq_sqrt (abs_nonneg _), one_mul]
       exact le_abs_self _ }, rfl, rfl, rfl⟩

end ATK.MaterialVacuity

end

#print axioms ATK.MaterialVacuity.producer_trivial
#print axioms ATK.MaterialVacuity.producer_any_terms
