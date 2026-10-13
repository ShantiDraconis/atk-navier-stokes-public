# Estado: CONDICIONAL — Navier–Stokes

Auditoria de 13/10/2026. Mesmo formato em todos os repositórios públicos ATK. Nada aqui afirma
prova nem refutação além do que o kernel certifica.

Legenda: **ABERTO** = alvo exato enunciável, nenhuma declaração desse tipo no kernel ·
**CONDICIONAL** = existe resultado que fecharia o alvo *se* uma hipótese explícita for
demonstrada · **NÃO_ENUNCIÁVEL** = o alvo exato não existe na Mathlib v4.34.1.

## 1. Alvo exato

Enunciado oficial (Fefferman/Clay): basta uma das alternativas (A) regularidade global sem força
em `ℝ³`, (B) idem no toro, (C) explosão com força suave em `ℝ³`, (D) idem no toro. Formalização
independente ATK (`audit/lean/ATK/Exact.lean`): `ClayA`, `ClayB`, `ClayC`, `ClayD`. No portão só
contam declarações de tipo exatamente uma delas ou `¬ ClayA` (a disjunção é teorema —
`navierStokes_disjunction` — e por isso não serve de alvo).

**Estado no portão:** (C) **CONDICIONAL** · (D) **CONDICIONAL** (ponte ainda não escrita) ·
(A) **ABERTO** · (B) **ABERTO**.

## 2. Itens condicionais — o que precisa ser arrumado

| # | Item | Estado | O que fechar |
|---|---|---|---|
| N1 | (C) pela prova formal da OpenAI (`openai/NavierStokesAndEuler@f9e8bc5`) | Q1 **verificado** (`clayC_of_fc`: o enunciado deles implica `ClayC`); Q2 (compila só com axiomas padrão?) em execução — ver `audit/README.md` | Resultado do kernel em Q2. Se passar, existe declaração de tipo exatamente `ClayC` (no toolchain deles) |
| N2 | (D) | Falta a ponte `navier_stokes_breakdown_periodic → ClayD`: é preciso conciliar as condições de força periódica das duas formalizações (domínio temporal, suavidade e decaimento em `t`) | Escrever e certificar a ponte (D), como foi feito para (C) |
| N3 | (A) e (B) — sem força | **Abertos.** Nenhum resultado de setembro de 2026 os decide (`clayA_false_iff`: uma explosão com força não é contraexemplo de (A)) | Prova de regularidade global sem força, ou dado suave sem força que explode |
| N4 | `NSMaterial.Closure` / `MaterialNSProducer` (`imports/Material/Closure.lean`) | **Vacuidade certificada** (`audit/lean/ATK/MaterialVacuity.lean`): habitada com tudo nulo (`producer_trivial`) e, mais forte, para QUAISQUER termos de estiramento dados (`producer_any_terms`), porque `nu`, `z`, `y` são campos livres | Ligar `nu` à viscosidade, `y` à enstrofia, `z` a `‖∇ω‖²` e `bulk + tail + remainder` ao estiramento de uma solução genuína; aí as cotas viram o conteúdo aberto |
| N5 | G1 `HypothesesComplete_v2.lean` | Honesto: `GeometricDepletion` é hipótese explícita; `EnstrophyData` são funções livres (por isso o registro diz "on genuine flow-derived EnstrophyData"). Modela o caso **sem força** — o balanço não tem termo de força | (i) produzir `EnstrophyData` de uma solução real; (ii) provar a depleção — conteúdo equivalente em força a (A)/(B); (iii) incluir o arquivo no CI |
| N6 | Prioridade | Separada da matemática: `imports/navier-stokes-critical-barrier-audit/PRIORITY.md` (não afirma acesso, derivação, plágio nem direito a prêmio) | — |

## 3. Falsificadores exatos

- (A) cai ⇔ existe `ν > 0` e dado `u₀` suave, `div u₀ = 0`, decaimento rápido, **sem força**, sem
  solução suave de energia limitada (`clayA_false_iff`); e então (C) vale (`clayA_or_clayC`).
- (C) da OpenAI cai se Q2 falhar (erro de compilação ou axioma fora de `propext`,
  `Classical.choice`, `Quot.sound`) — o que não refutaria (C), só aquela prova.

## 4. Prêmio

Regras do Clay: publicação qualificada, pelo menos dois anos e aceitação geral; não há submissão
direta. Em 11/9/2026 o Clay disse que o problema "has apparently been settled" e que a avaliação
está em curso; nenhum prêmio atribuído. Nada neste repositório altera isso.

---

**English summary.** Clay (C): CONDITIONAL on the external kernel build (statement faithfulness
already verified by `clayC_of_fc`). (D): bridge pending. (A)/(B), the unforced alternatives: OPEN.
Kernel-certified finding: the imported `NSMaterial.Closure` is vacuous (any stretching terms fit
the budget because `nu`, `z`, `y` are free fields). The G1 hypotheses file is honest but its data
must come from a genuine solution.
