# Estado: Navier–Stokes — (C) e (D) FECHADOS por prova externa · (A)/(B) ABERTOS

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

**Estado no portão:** (C) **FECHADO por prova externa** — `atk_clayC_certified : ATK.Exact.ClayC`
verificado pelo kernel no ambiente da OpenAI (run `38376347284`; ver `audit/README.md`) ·
(D) **FECHADO por prova externa** — `atk_clayD_certified : ATK.Exact.ClayD` (ponte `clayD_of_fc`; run `38382016251`) ·
(A) **ABERTO** · (B) **ABERTO**.

## 2. Itens condicionais — o que precisa ser arrumado

| # | Item | Estado | O que fechar |
|---|---|---|---|
| N1 | (C) pela prova formal da OpenAI (`openai/NavierStokesAndEuler@f9e8bc5`) | Q1 **verificado** (`clayC_of_fc`); Q2 **verificado**: compila em 32 min, só axiomas padrão; `atk_clayC_certified : ClayC` aceito pelo kernel no toolchain deles (`v4.34.0-rc2`) | Opcional: reproduzir no toolchain ATK (`v4.34.1`). A prova é da OpenAI (e há provas humanas independentes); não é do programa ATK |
| N2 | (D) | **Feito**: `clayD_of_fc` (6/6 no kernel ATK; força estendida `f(x, max t 0)`); `atk_clayD_certified : ClayD` aceito pelo kernel no ambiente deles (run `38382016251`) | — |
| N3 | (A) e (B) — sem força | **Abertos.** Nenhum resultado de setembro de 2026 os decide (`clayA_false_iff`: uma explosão com força não é contraexemplo de (A)) | Prova de regularidade global sem força, ou dado suave sem força que explode |
| N4 | `NSMaterial.Closure` / `MaterialNSProducer` (`imports/Material/Closure.lean`) | **Não compila como está** (campos múltiplos sem parênteses viram parâmetros do primeiro campo). Na intenção evidente: **vacuidade certificada** (`audit/lean/ATK/MaterialVacuity.lean`): habitada com tudo nulo (`producer_trivial`) e, mais forte, para QUAISQUER termos de estiramento dados (`producer_any_terms`), porque `nu`, `z`, `y` são campos livres | Ligar `nu` à viscosidade, `y` à enstrofia, `z` a `‖∇ω‖²` e `bulk + tail + remainder` ao estiramento de uma solução genuína; aí as cotas viram o conteúdo aberto |
| N5 | G1 `HypothesesComplete_v2.lean` | Honesto: `GeometricDepletion` é hipótese explícita; `EnstrophyData` são funções livres (por isso o registro diz "on genuine flow-derived EnstrophyData"). Modela o caso **sem força** — o balanço não tem termo de força | (i) produzir `EnstrophyData` de uma solução real; (ii) provar a depleção — conteúdo equivalente em força a (A)/(B); (iii) incluir o arquivo no CI |
| N6 | Prioridade | Separada da matemática: `imports/navier-stokes-critical-barrier-audit/PRIORITY.md` (não afirma acesso, derivação, plágio nem direito a prêmio) | — |

## 2b. Linha de explosão — certificada no kernel

No NS a explosão é literal. `audit/lean/ATK/NSExplosion.lean` e `NSBridgeD.lean`:

| Alternativa | Explosão | Estado |
|---|---|---|
| (C) ℝ³, com força | `clayC_of_fc` + prova da OpenAI | **realizada** (kernel, ambiente deles) |
| (D) toro, com força | `clayD_of_fc` (6/6 certificado) + prova da OpenAI | **realizada** (kernel, ambiente deles) |
| (A) ℝ³, sem força | `UnforcedBlowupR3`; `clayA_iff_no_explosion`; `explosion_gives_C` | **nenhuma testemunha conhecida** |
| (B) toro, sem força | `UnforcedBlowupTorus`; `clayB_iff_no_explosion` | **nenhuma testemunha conhecida** |

## 2c. Linha de fechamento — CLOSED_MATH calculado pelo kernel

Mesmo formato das linhas condicional e de explosão: **alvo exato** → **certificado** (declaração
sem hipóteses, de tipo exatamente o alvo) → **portão** (`audit/lean/scripts/closure_gate.py`:
kernel + axiomas padrão + controles) → **bandeira** calculada, nunca escrita à mão.

| Alegação | Alvo exato | CLOSED_MATH | Certificado | Rotas certificadas até ela |
|---|---|---|---|---|
| C | `ATK.Exact.ClayC` | **true** (ambiente externo) | `atk_clayC_certified` | ponte `clayC_of_fc` + prova da OpenAI |
| D | `ATK.Exact.ClayD` | **true** (ambiente externo) | `atk_clayD_certified` | ponte `clayD_of_fc` + prova da OpenAI |
| A | `ATK.Exact.ClayA` | **false** | — | nenhuma |
| ¬A | `¬ ATK.Exact.ClayA` | **false** | — | explosão `explosion_refutes_A` (sem testemunha) |
| B | `ATK.Exact.ClayB` | **false** | — | nenhuma |
| ¬B | `¬ ATK.Exact.ClayB` | **false** | — | explosão `explosion_refutes_B` (sem testemunha) |

Controles do portão (todos OK, run `38387829549`): aceita uma decisão verdadeira de problema-brinquedo;
recusa alvo como `axiom`; recusa `sorry`; recusa a ponte e a linha de explosão oferecidas como
certificado (falta H / falta a testemunha); recusa `alvo ∨ ¬alvo` (teorema vazio).

Os certificados de (C) e (D) só existem no ambiente da OpenAI (a prova deles não compila no
toolchain ATK v4.34.1 sem portar o repositório). Por isso o portão roda duas vezes: no ambiente
ATK (`registry.json`: C e D sem certificado local, só rotas) e no ambiente externo
(`registry_external.json`, workflow `audit-openai-external`, run `38387829506`: **C = true, D = true,
portão VÁLIDO**, mesmos controles).

Para mudar uma bandeira para `true`, basta acrescentar a `audit/lean/closure/registry.json`
uma declaração que o kernel aceite com o tipo exato — vinda de uma prova de H (pela ponte) ou de
uma testemunha (pela explosão). Nenhuma outra edição altera o resultado.

## 3. Falsificadores exatos

- (A) cai ⇔ existe `ν > 0` e dado `u₀` suave, `div u₀ = 0`, decaimento rápido, **sem força**, sem
  solução suave de energia limitada (`clayA_false_iff`); e então (C) vale (`clayA_or_clayC`).
- (C): Q2 passou. O que ainda pode invalidar a verificação é só a base de confiança (kernel do
  Lean, definições da Mathlib e de `ATK/Exact.lean`), não a prova.

## 4. Prêmio

Regras do Clay: publicação qualificada, pelo menos dois anos e aceitação geral; não há submissão
direta. Em 11/9/2026 o Clay disse que o problema "has apparently been settled" e que a avaliação
está em curso; nenhum prêmio atribuído. Nada neste repositório altera isso.

---

**English summary.** Clay (C): CLOSED by an external proof — `atk_clayC_certified : ATK.Exact.ClayC`
is accepted by the Lean kernel in OpenAI's environment (standard axioms only). (D): CLOSED the same way —
`atk_clayD_certified : ATK.Exact.ClayD` via the bridge `clayD_of_fc`. (A)/(B), the unforced alternatives: OPEN.
Kernel-certified finding: the imported `NSMaterial.Closure` is vacuous (any stretching terms fit
the budget because `nu`, `z`, `y` are free fields). The G1 hypotheses file is honest but its data
must come from a genuine solution.
