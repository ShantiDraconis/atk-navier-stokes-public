# Auditoria independente — prova de explosão de Navier–Stokes anunciada pela OpenAI (8/9/2026)

**Estado desta auditoria: Q1, Q2 e Q3 VERIFICADOS (13/10/2026).** Resultado: a prova formal da
OpenAI compila só com os axiomas padrão, e no mesmo ambiente o kernel aceitou uma declaração de
tipo exatamente `ATK.Exact.ClayC`. As alternativas sem força (A) e (B) continuam abertas.

| Pergunta | Como é verificada | Estado |
|---|---|---|
| Q1. O enunciado formal deles diz o que o Clay pede em (C)? | Ponte provada no kernel: o enunciado deles ⇒ formalização independente ATK de (C) | **VERIFICADO** (`ATK.NSBridge.clayC_of_fc`) |
| Q2. A prova Lean deles compila, sem `sorry` e só com os axiomas padrão? | Compilação do repositório deles no ambiente deles + `#print axioms` | **VERIFICADO** (run `38376347284`, ver abaixo) |
| Q3. O que o resultado NÃO decide? | Teoremas do kernel sobre (A), (B), (C) | **VERIFICADO** (ver abaixo) |

## Objeto auditado

- Anúncio: OpenAI, 8/9/2026 — explosão em tempo finito para Navier–Stokes 3D incompressível com
  força externa suave, a partir de dado em repouso; reivindica as alternativas **(C)** (ℝ³) e
  **(D)** (ℝ³/ℤ³) do enunciado oficial de Fefferman/Clay.
- Clay Mathematics Institute, 11/9/2026: o problema "has apparently been settled"; avaliação em
  curso; nenhum prêmio atribuído.
- Formalização: `github.com/openai/NavierStokesAndEuler`, commit `f9e8bc5` (10/9/2026),
  Lean `v4.34.0-rc2`, 816 arquivos em `NavierStokes/`; revisão declarada "self-assessed".
  Varredura textual (13/10/2026): 0 ocorrências de `sorry`/`admit`, 0 declarações `axiom`,
  0 usos de `native_decide`/`implemented_by`/`extern`/`unsafe` em `NavierStokes/`.
  Isso NÃO substitui a compilação (Q2).

## Q1 — fidelidade do enunciado (verificado)

A forma mais comum de uma "prova formal" de um problema famoso não valer é o enunciado formal ser
mais fraco que o original (definições com brechas, valores-lixo, classes de solução restritas).
Testamos isso contra uma formalização **independente**, escrita antes de conhecer a deles
(`ATK/Exact.lean`: derivadas parciais, divergência, Laplaciano, gradiente, energia por integral de
Lebesgue, tempo antes do espaço).

`ATK/NSBridge.lean` prova, só com Mathlib e axiomas padrão:

- divergência, Laplaciano, gradiente e termo convectivo ATK = operadores intrínsecos da Mathlib
  usados por eles;
- as condições de dado e força deles implicam as nossas (expoente real ⇒ natural; a troca
  `(x,t) ↔ (t,x)` é isometria);
- **toda solução no sentido ATK é solução no sentido deles** — logo "não existe solução deles"
  implica "não existe solução ATK";
- `clayC_of_fc : FCBreakdownR3 → ATK.Exact.ClayC`.

Conclusão de Q1: o enunciado deles não é mais fraco que (C). Com Q2 verificado, a alternativa
(C) do Clay, na formalização ATK, está demonstrada (no ambiente deles).

`ATK/FCNavierStokes.lean` é cópia verbatim (Apache-2.0) das definições
`NavierStokes/ComparatorDefinitions.lean` deles (sha256 `8d90e0f9…6ebf4`), com nota de proveniência.

## Q2 — a prova compila? (verificado)

Resultado do workflow `audit-openai-external`, run `38376347284` (13/10/2026, commit auditado
`f9e8bc5`, Lean `v4.34.0-rc2` com a Mathlib fixada por eles):

| Passo | Resultado |
|---|---|
| Compilar `NavierStokes.ComparatorSolution` (fechamento de dependências) | **sucesso**, 32 min (09:29–10:01 UTC) |
| `#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic` | `[propext, Classical.choice, Quot.sound]` |
| `atk_clayC_certified : ATK.Exact.ClayC := clayC_of_fc navier_stokes_breakdown_R3` | **compilou**; axiomas exatamente `[propext, Classical.choice, Quot.sound]` |

Leitura: a alternativa **(C)** do Clay, na formalização independente ATK, é um **teorema
verificado pelo kernel do Lean** — no ambiente da OpenAI (`v4.34.0-rc2`), com a prova deles e a
ponte ATK. A base de confiança é: o kernel do Lean, as definições da Mathlib usadas, as
definições ATK de `ATK/Exact.lean` e a ponte `ATK/NSBridge.lean` (as duas últimas auditáveis
aqui). Isto é verificação formal, não decisão do Clay: o prêmio segue as regras do instituto
(publicação qualificada, dois anos, aceitação geral). (D): os axiomas do teorema periódico deles
também são os padrão, mas a ponte ATK para `ClayD` ainda não foi escrita.

Como o workflow faz:
1. clona o commit auditado e registra sha256 das definições;
2. compila `NavierStokes.ComparatorSolution` com o toolchain deles;
3. imprime e checa os axiomas de `navier_stokes_breakdown_R3` e `navier_stokes_breakdown_periodic`
   (aceita só `propext`, `Classical.choice`, `Quot.sound`);
4. no mesmo ambiente, compila `atk_clayC_certified : ATK.Exact.ClayC :=
   clayC_of_fc navier_stokes_breakdown_R3`.


## Q3 — (A) e (B) em xeque: o que o resultado não decide (verificado)

Teoremas de `ATK/Closure.lean`, certificados pelo kernel:

- `clayA_or_clayC : ClayA ∨ ClayC` — a disjunção oficial é um **teorema**: se (A) falha para algum
  ν e algum dado, a reescala `v(t,x) = a·u(a t, x)` (viscosidade `a·ν`) transporta a falha a todo
  ν, e com força nula isso já é (C). Portanto o enunciado do Clay, que aceita qualquer uma das
  alternativas (A)–(D), pode ser decidido por uma construção **com força** sem tocar em (A).
- `clayA_false_iff`: (A) é falsa ⇔ existe ν > 0 e dado suave, de divergência nula e decaimento
  rápido, **sem força**, sem solução suave de energia limitada. Uma explosão com força (C) não é
  um contraexemplo de (A): o dado da OpenAI parte do repouso, e com força nula esse dado gera a
  solução nula, global e suave — a força externa suave é parte essencial da construção.
- `navierStokes_disjunction`: o `Prop` "A ∨ B ∨ C ∨ D" é demonstrável; por isso o fechamento é
  medido por declarações de tipo exatamente `ClayA`, `ClayB`, `ClayC`, `ClayD` ou `¬ClayA`.

Leitura: com Q2 confirmado, **(A) e (B) — regularidade global sem força, em ℝ³ e no
toro — continuam ABERTAS**. É a pergunta física central (há explosão espontânea no fluido sem
força externa?) e nenhum dos resultados anunciados em setembro de 2026 a decide.

## Prioridade

Ver `imports/navier-stokes-critical-barrier-audit/PRIORITY.md`. Esta auditoria é matemática e
independente de qualquer questão de prioridade; não afirma acesso, derivação, plágio ou direito a
prêmio.

---

**English summary.** Independent audit of OpenAI's announced finite-time blow-up for forced 3D
Navier–Stokes (Clay alternatives (C)/(D)). Q1 (statement faithfulness): VERIFIED — a kernel-checked
bridge proves their formal statement implies an independently written ATK formalization of Clay (C).
Q2: VERIFIED — their 816-file proof builds in their toolchain (Lean v4.34.0-rc2) in 32 minutes;
`navier_stokes_breakdown_R3` and `_periodic` depend only on propext, Classical.choice, Quot.sound;
in the same environment `atk_clayC_certified : ATK.Exact.ClayC` compiles with the same axioms. Q3: kernel theorems show the official disjunction (A)∨(C) is provable, so
a forced construction settles the Clay problem as stated but leaves the unforced alternatives (A)/(B)
open. No priority, plagiarism or prize claim is made.
