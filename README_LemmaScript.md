# opencode — Verified with LemmaScript

Fork of [opencode-ai/opencode](https://github.com/opencode-ai/opencode) with two pieces of production permission-system logic verified in-place against the [LemmaScript](https://github.com/midspiral/LemmaScript) Dafny backend. The function bodies and signatures are untouched; everything is added through `//@` annotation comments.

Two functions, seven verification conditions, zero errors. The case study drove substantial LemmaScript additions — auto-extern for cross-file calls, spec lifting onto axiom declarations, declare-type aliases, dotted-name fallback — see [Notes for LemmaScript](#notes-for-lemmascript). In scope: the access-control core; out of scope (for now): the runtime state machine sitting on top.

## What's Verified

### `evaluate` — `packages/opencode/src/permission/evaluate.ts` (in-place)

The "last-matching rule wins, otherwise ask" core of opencode's permission engine. Body and signature unchanged; two `//@ ensures` clauses pin both directions of the spec.

```ts
export function evaluate(permission: string, pattern: string, ...rulesets: Rule[][]): Rule {
  //@ ensures forall(i: nat, i < rulesets.flat().length ==> !(Wildcard.match(permission, rulesets.flat()[i].permission) && Wildcard.match(pattern, rulesets.flat()[i].pattern))) ==> \result.permission === permission && \result.pattern === "*" && \result.action === "ask"
  //@ ensures exists(j: nat, j < rulesets.flat().length && Wildcard.match(permission, rulesets.flat()[j].permission) && Wildcard.match(pattern, rulesets.flat()[j].pattern)) ==> exists(k: nat, k < rulesets.flat().length && \result === rulesets.flat()[k] && Wildcard.match(permission, \result.permission) && Wildcard.match(pattern, \result.pattern) && forall(m: nat, k < m && m < rulesets.flat().length ==> !(Wildcard.match(permission, rulesets.flat()[m].permission) && Wildcard.match(pattern, rulesets.flat()[m].pattern))))
  const rules = rulesets.flat()
  const match = rules.findLast(
    (rule) => Wildcard.match(permission, rule.permission) && Wildcard.match(pattern, rule.pattern),
  )
  return match ?? { action: "ask", permission, pattern: "*" }
}
```

**Verified properties:**

- **Default-iff-no-match.** If no rule in the flattened ruleset matches `(permission, pattern)` under `Wildcard.match`, the result is the synthesized `{ permission, pattern: "*", action: "ask" }` default. Safe-by-default: empty or non-matching rulesets never produce an `allow`.
- **Last-wins.** If some rule matches, the result equals `rulesets.flat()[k]` for the **maximal** matching index, and no later rule matches. This is the property that makes ordering load-bearing — appending a deny at the end of the ruleset guarantees every subsequent matching query becomes that deny, regardless of earlier allows.

Both ensures are parametric over `Wildcard.match`, which is auto-externed (regex-based, out of LemmaScript's model — see [Notes](#notes-for-lemmascript)). The proof is invariant under any choice of matcher.

4 VCs, 0 errors.

### `deriveSubagentSessionPermission` — `packages/opencode/src/agent/subagent-permissions.ts` (in-place)

Builds the permission ruleset for a subagent's session, combining parent-agent edit-denies, parent-session denies, and default `task`/`todowrite` denies. Introduced by [opencode #26514](https://github.com/sst/opencode/issues/26514) — subagents spawned via the task tool were silently bypassing Plan Mode's file-edit restriction because Plan Mode's denies live on the agent ruleset, not the session.

```ts
export function deriveSubagentSessionPermission(input: {
  parentSessionPermission: Permission.Ruleset
  parentAgent: Agent.Info | undefined
  subagent: Agent.Info
}): Permission.Ruleset {
  //@ type input SubInput
  //@ ensures forall(j: nat, j < \result.length ==> !(\result[j].permission === "edit" && \result[j].action === "allow"))
  // ... body unchanged ...
}
```

**Verified property (safety direction):**

- **No edit-allows in the output.** For all `j`, `\result[j]` is *not* a `{ permission: "edit", action: "allow" }` rule. The function can only emit denies (and `external_directory` rules from the session) for the `edit` permission; it never introduces an allow.

This is the **safety consequence** of #26514's fix: even if the toolchain composes `deriveSubagentSessionPermission` with `evaluate`, no subagent can obtain an `edit`-allow through this function — there's nothing to override the parent's denies with.

3 VCs, 0 errors.

## What We Did *Not* Prove (and Why)

The natural strengthening — "every parent edit-deny appears in `\result`" (the **completeness direction** of deny inheritance) — was attempted and abandoned. The blocker:

**Dafny does not equate textually-identical anonymous lambdas.** A 5-line test confirms `Filter((x: int) => x > 0, s)` in a function body and `Filter((x: int) => x > 0, s)` in a proof evaluate to `Filter` applied to *different* function values, even with the same parameter name and body. A helper lemma proving membership in `Filter(λ_in_helper, perm)` therefore can't transport its conclusion onto the `Filter(λ_in_function_body, perm)` call inside `deriveSubagentSessionPermission`'s body — Dafny treats the two `Filter` applications as unrelated.

The two existing LemmaScript case studies that use `Std.Collections.Seq.Filter` ([collab-todo](https://github.com/midspiral/collab-todo-lemmascript), [mastra](https://github.com/midspiral/mastra-lemmascript)) work around this by stating only **soundness-direction** specs (`x ∈ filter(p, s) ⟹ p(x)`), which is what `Std.Collections.Seq.Filter`'s stdlib `ensures` directly provides. Nothing in the corpus has proved completeness through a filter.

The clean LemmaScript-side fix is **lambda lifting** in `dafny-emit.ts`: emit each filter/some/every lambda as a top-level `predicate FilterPred_<fn>_<n>(...) { ... }` and replace the lambda at the call site with the predicate name. Then both the function body and any proof reference the same named symbol and the equality wall vanishes. Roughly 30–50 LOC. Not done in this case study; left as the next LS investment.

The current spec on `deriveSubagentSessionPermission` captures the operationally critical half of #26514 (no edit-allow can be produced) but not the structural half (every parent edit-deny is preserved). Both halves together would close the loop end-to-end.

## Caveats

- **`Wildcard.match` is opaque.** Both `evaluate.ts`'s proofs are parametric over the matcher. They hold for any total `(string, string) → boolean`. The actual regex-based implementation in `util/wildcard.ts` is unverifiable in LemmaScript today (regex modeling is out of scope); but every theorem stated transfers unchanged if `Wildcard.match` is later replaced by a hand-written verifiable glob matcher.
- **`Schema.X` typings don't expand through ts-morph.** opencode uses `Schema.Struct(...)` and `Schema.Schema.Type<typeof X>` pervasively. ts-morph (LemmaScript's frontend) sees these as `Type<any>` — the type-level computation doesn't get followed. `subagent-permissions.ts` works around this with four `//@ declare-type` shim lines that give LemmaScript a simplified view of `Rule`, `Info`, `Ruleset`, and the input-record shape.
- **Subagent-permissions spec is a single direction.** See the section above.

## Setup

**Prerequisites:** [Dafny](https://github.com/dafny-lang/dafny) ≥ 4.0 with standard libraries, Node.js ≥ 18.

```sh
git clone https://github.com/midspiral/LemmaScript.git ../LemmaScript
cd ../LemmaScript/tools && npm install && cd -
./LemmaScript/tools/check.sh dafny
```

`subagent-permissions.ts` requires `--standard-libraries` (uses `Std.Collections.Seq.Filter`); the per-file entries in `LemmaScript-files.txt` carry the flag.

## File Structure

```
packages/opencode/src/permission/evaluate.ts          ← In-place, 2 ensures
packages/opencode/src/permission/evaluate.dfy.gen     ← Regeneratable
packages/opencode/src/permission/evaluate.dfy         ← Verified

packages/opencode/src/agent/subagent-permissions.ts       ← In-place, 1 ensures + 4 declare-type shims
packages/opencode/src/agent/subagent-permissions.dfy.gen  ← Regeneratable
packages/opencode/src/agent/subagent-permissions.dfy      ← Verified
```

## Notes for LemmaScript

The case study drove these additions to LemmaScript itself:

**Toolchain features:**
- **Auto-extern for cross-file calls.** When `lsc` sees `Wildcard.match(a, b)` and ts-morph resolves the callee to another `.ts` file, an opaque `function {:axiom} Wildcard_match(...)` is emitted in the Dafny output and call sites are rewritten. No annotation required; the `import` statement is the entire signal. Both namespaced (`X.y`) and bare-name (`foo`) imports are auto-resolved, with `.d.ts` declarations skipped. (`extract.ts`)
- **Cross-file spec lifting.** `//@ requires` / `//@ ensures` on a cross-file callee's declaration are copied onto the axiom in the calling file's output, so callers reason against the source's verified contract instead of an unconstrained axiom. Transitive through nested cross-file references in the lifted specs. (`extract.ts` + `resolve.ts` + `transform.ts` + `dafny-emit.ts`)
- **`Array.prototype.findLast`** with full completeness `ensures` on the preamble (returns the rightmost matching element; characterizes the index as maximal). (`dafny-emit.ts` + `resolve.ts`)
- **`Array.prototype.flat`** with the `seq<seq<T>> → seq<T>` flattening preamble. (`dafny-emit.ts`)
- **Rest parameters typed `T[][]`.** No change needed — ts-morph's read of `...args: T[]` becomes the parameter type directly.
- **`//@ declare-type Name = TsType` alias form.** Companion to the existing record form `//@ declare-type Name { ... }`. Used for `Ruleset = Rule[]`. (`extract.ts`)
- **Dotted user-type lookup with last-segment fallback.** `Agent.Info` and `Permission.Ruleset` resolve to `//@ declare-type Info { ... }` / `Ruleset` via the trailing identifier. (`resolve.ts`)
- **Alias expansion for structural targets.** When an alias points to an array/map/set/optional/user type, references to the alias are expanded so downstream code doesn't need to follow indirection. Primitive-targeted aliases like `type TaskId = number` are preserved (avoid regressing the generated Dafny for case studies that use them). (`resolve.ts`)

**Bug fixes uncovered along the way:**
- **Record literal emission was field-position-order, not struct-order.** `{ action: "ask", permission, pattern: "*" }` was emitting as `Rule("ask", permission, "*")` against a `Rule(permission, pattern, action)` declaration — silently misassigning all three fields. The `evaluate.ts` spec exposed it on the `None`-branch default. (`dafny-emit.ts`)
- **`\result` narrowing through `==>` premises.** `//@ ensures \result !== undefined ==> P(\result)` wasn't firing the optional-narrowing rule because `\result` is `kind: "result"` in raw IR, not `kind: "var"`. (`resolve.ts`)
- **Quantifier left-operand parens in binop emission.** `forall i :: A || B` parses as `forall i :: (A || B)` in Dafny — the body extends as far as possible. The emitter now wraps quantifier-typed left operands in binops. (`dafny-emit.ts`)
- **`inferLambdaParamTypes` not applied in `optChain` call steps.** A lambda buried inside `obj?.filter(r => ...)` got `int`-typed params instead of the array's element type, breaking the deny-inheritance proof until fixed. (`resolve.ts`)

**Pending (not done):**
- **Lambda lifting for filter predicates.** Would unblock the completeness direction of the deny-inheritance theorem (see [What We Did Not Prove](#what-we-did-not-prove-and-why)).
- **Schema-aware extraction.** Would remove the need for `//@ declare-type` shims when the upstream types are Schema-derived. Likely 200–300 LOC; not strictly necessary given the shim workaround.
