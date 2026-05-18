# opencode — Verified with LemmaScript

Fork of [opencode-ai/opencode](https://github.com/opencode-ai/opencode) with two pieces of production permission-system logic verified in-place against the [LemmaScript](https://github.com/midspiral/LemmaScript) Dafny backend. The function bodies and signatures are untouched; everything is added through `//@` annotation comments.

Two functions, nine verification conditions, zero errors. The case study drove substantial LemmaScript additions — auto-extern for cross-file calls, spec lifting onto axiom declarations, declare-type aliases, dotted-name fallback — see [Notes for LemmaScript](#notes-for-lemmascript). In scope: the access-control core; out of scope (for now): the runtime state machine sitting on top.

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

**Verified properties (both directions of deny inheritance):**

- **Safety: no edit-allows in the output.** For all `j`, `\result[j]` is *not* a `{ permission: "edit", action: "allow" }` rule. The function can only emit denies (and `external_directory` rules from the session) for the `edit` permission; it never introduces an allow.
- **Completeness: every parent edit-deny is preserved.** When `parentAgent` is defined, for every index `i` where `parentAgent.permission[i]` is an edit-deny, that exact rule appears somewhere in `\result`. The fix for #26514 doesn't just *avoid* introducing allows; it actively *carries forward* every relevant deny.

Together these close the loop on #26514 mechanically: parent edit-denies are in the output (completeness), and nothing else can override them (safety).

5 VCs, 0 errors. Completeness requires a 10-line proof body in the `.dfy` file (a recursive helper plus its invocation under the `Some` branch); the safety direction discharges automatically.

## How the Completeness Direction Proves

`deriveSubagentSessionPermission`'s body uses an inline `.filter(rule => rule.action === "deny" && rule.permission === "edit")` lambda. Dafny does *not* equate textually-identical anonymous lambdas — a helper lemma proving membership in `Filter(λ_in_helper, perm)` cannot transport its conclusion onto the `Filter(λ_in_function_body, perm)` inside the function. This wall blocks the obvious "invoke a separately-proved filter-membership helper" pattern; both existing LemmaScript case studies that use `Seq.Filter` ([collab-todo](https://github.com/midspiral/collab-todo-lemmascript), [mastra](https://github.com/midspiral/mastra-lemmascript)) work around it by stating only soundness-direction specs.

The workaround that *does* go through: write the helper lemma to take *the same `input`* the main function takes, and recurse on the perm sequence's length by building a `smallerInput` with `parentAgent.permission[1..]`. Both the original and recursive `deriveSubagentSessionPermission(...)` calls reference the same function symbol, so Dafny's function-unfolding gives each invocation access to the same inline filter lambda — the lambda equality wall is never hit. `reveal Std.Collections.Seq.Filter()` lets Dafny step through Filter's structure inductively. The full proof in `subagent-permissions.dfy` is:

```dafny
lemma DenyInheritStep(input: SubInput, pa: Info, i: nat)
  requires input.parentAgent == Some(pa)
  requires i < |pa.permission|
  requires pa.permission[i].action == "deny" && pa.permission[i].permission == "edit"
  ensures pa.permission[i] in deriveSubagentSessionPermission(input)
  decreases |pa.permission|
{
  reveal Std.Collections.Seq.Filter();
  if i > 0 {
    var smallerPa := Info(pa.permission[1..]);
    var smallerInput := SubInput(input.parentSessionPermission, Some(smallerPa), input.subagent);
    DenyInheritStep(smallerInput, smallerPa, i - 1);
  }
}
```

This sidesteps the lambda-equality issue entirely — no LemmaScript-side lambda lifting needed.

## Caveats

- **`Wildcard.match` is opaque.** Both `evaluate.ts`'s proofs are parametric over the matcher. They hold for any total `(string, string) → boolean`. The actual regex-based implementation in `util/wildcard.ts` is unverifiable in LemmaScript today (regex modeling is out of scope); but every theorem stated transfers unchanged if `Wildcard.match` is later replaced by a hand-written verifiable glob matcher.
- **`Schema.X` typings don't expand through ts-morph.** opencode uses `Schema.Struct(...)` and `Schema.Schema.Type<typeof X>` pervasively. ts-morph (LemmaScript's frontend) sees these as `Type<any>` — the type-level computation doesn't get followed. `subagent-permissions.ts` works around this with four `//@ declare-type` shim lines that give LemmaScript a simplified view of `Rule`, `Info`, `Ruleset`, and the input-record shape.

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
- **Schema-aware extraction.** Would remove the need for `//@ declare-type` shims when the upstream types are Schema-derived. Likely 200–300 LOC; not strictly necessary given the shim workaround.
- **Lambda lifting for filter predicates.** Initially thought necessary for the completeness direction of deny-inheritance, but the recursive-helper-with-same-function-symbol pattern (see [How the Completeness Direction Proves](#how-the-completeness-direction-proves)) sidesteps the lambda-equality wall without any LS-side change. Lambda lifting would let auto-discharge replace the manual 10-line proof body in cases where the lifted predicate has no free variables; nice-to-have but not blocking.
