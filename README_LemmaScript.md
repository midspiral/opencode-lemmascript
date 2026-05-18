# opencode — Verified with LemmaScript

Fork of [anomalyco/opencode](https://github.com/anomalyco/opencode) applying [LemmaScript](https://github.com/midspiral/LemmaScript)'s Dafny backend to opencode's permission system. Annotations are added in-place — function bodies and signatures stay unchanged; everything goes through `//@` comments. Work in progress.

Currently verified: five functions, zero errors. The case study drove substantial LemmaScript additions — auto-extern for cross-file calls, spec lifting onto axiom declarations, declare-type aliases, dotted-name fallback, C-style for-loop desugaring, map literals, JS-safe slice, brownfield `//@ verify` extraction with continue-rewrite and function-scoped extern registration, in-file `//@ extern` declarations, array-destructuring with rest at let-statement level — see [Notes for LemmaScript](#notes-for-lemmascript).

## What's Verified

### `evaluate` — `packages/opencode/src/permission/evaluate.ts`

The "last-matching rule wins, otherwise ask" core of opencode's permission engine. Two `//@ ensures` clauses pin both directions of the spec, parametric over `Wildcard.match` (auto-externed; regex-based, treated as an opaque predicate).

- **Default-iff-no-match.** No rule matches `(permission, pattern)` ⟹ the result is the synthesized `{ permission, pattern: "*", action: "ask" }` default. Empty or non-matching rulesets never produce an `allow`.
- **Last-wins.** Some rule matches ⟹ the result equals `rulesets.flat()[k]` for the **maximal** matching index, and no later rule matches. Appending a deny at the end of the ruleset guarantees every subsequent matching query becomes that deny, regardless of earlier allows.

4 VCs, 0 errors.

### `deriveSubagentSessionPermission` — `packages/opencode/src/agent/subagent-permissions.ts`

Builds a subagent's session ruleset by combining parent-agent edit-denies, parent-session denies, and default `task`/`todowrite` denies. Introduced by [opencode #26514](https://github.com/sst/opencode/issues/26514) — subagents spawned via the task tool were silently bypassing Plan Mode's file-edit restriction because Plan Mode's denies live on the agent ruleset, not the session.

Both directions of deny-inheritance proven:

- **Safety: no edit-allows in the output.** For all `j`, `\result[j]` is not a `{ permission: "edit", action: "allow" }` rule. The function never introduces an allow on `edit`.
- **Completeness: every parent edit-deny is preserved.** When `parentAgent` is defined, every `parentAgent.permission[i]` with `action === "deny" && permission === "edit"` appears somewhere in `\result`.

Together these close #26514 mechanically: every parent edit-deny carries forward, and nothing else can override them.

5 VCs, 0 errors. Completeness needs a 10-line proof body in the `.dfy` file (a recursive helper that recurses on `parentAgent.permission`'s length); safety discharges automatically.

### `BashArity.prefix` — `packages/opencode/src/permission/arity.ts`

Extracts the "human-understandable command" from a shell token list using a longest-prefix-wins lookup against the static `ARITY` dictionary (160 entries: `npm` → 2, `npm run` → 3, `git config` → 3, etc.). Used by the permission system to attach allow/deny rules to the right logical command — e.g., so a rule on `npm run dev` matches whether the user typed `npm run dev` or `npm run dev --watch`.

**Structural properties** as three `//@ ensures` clauses on the function:

- **Bounded length.** `\result.length <= tokens.length`.
- **Prefix.** `\result[i] === tokens[i]` for every `i < \result.length`. Combined with the bound, the result is literally `tokens[0..\result.length]`.
- **Empty in → empty out.** `tokens.length === 0 ==> \result.length === 0`.

**Longest-match property**, proven as a freestanding Dafny lemma in `arity.dfy`:

> If `k` is the maximal length in `[1, |tokens|]` for which `SeqJoin(tokens[0..k], " ") in ARITY`, then `longestMatchPrefix(tokens) == SafeSlice(tokens, 0, ARITY[that joined prefix])`.

That is: the algorithm returns the slice indicated by the *longest* matching dictionary entry. Proven via an auxiliary lemma `LongestMatchReduce(tokens, len, k)` that shows the loop's downward sweep reduces to a fixed length: starting from any `len in [k, |tokens|]`, the recursion peels back one length at a time until it hits `k`, the longest match.

The lemma proves the property about a Dafny *mirror function* `longestMatchPrefix` that statement-for-statement matches the production code; the production `prefix` is a method (its body is opaque to external lemmas), so the connection is by code inspection rather than mechanical refinement. The mirror function is itself defined in `arity.dfy` next to the lemma.

10 VCs, 0 errors. The body is a decrementing C-style `for` loop over prefix lengths; LS desugars it to a `while` automatically.

### `Permission.disabled` — `packages/opencode/src/permission/index.ts`

The "which input tools have a wildcard-deny rule" check used to gate the tool list. For each `tool`, collapses edit-class tools (`edit` / `write` / `apply_patch`) to a single `"edit"` permission, finds the last rule whose `permission` field matches via `Wildcard.match`, and emits the tool iff that last rule has `pattern === "*"` and `action === "deny"`. Annotated in-place inside `permission/index.ts` — the big `Layer.effect`/`Effect.gen` service file — using LS's brownfield `//@ verify` extraction so the surrounding state machine is bypassed.

Both directions of the deny-characterization proven, parametric over `Wildcard.match`:

- **Necessary.** If `tool ∈ \result`, then there exists a maximal-index rule in `ruleset` matching `permission(tool)` with `pattern === "*"` and `action === "deny"`.
- **Sufficient.** If such a maximal matching deny rule exists for some `tools[i]`, then `tools[i] ∈ \result`.

Three `//@ invariant` clauses on the `for (const tool of tools)` loop carry the proof: a strengthened soundness invariant `t ∈ result ⟹ ∃ j < _tool_idx. tools[j] === t` (so prior-iteration witnesses transfer across same-string duplicates), plus both directions of the deny-witness restricted to `j < _tool_idx`. A single hand-added `assert` in `.dfy` names the `SeqFindLast` witness inside the `*`-deny branch, letting Dafny discharge the necessary-direction maintenance.

### `Wildcard.matchSequence` — `packages/opencode/src/util/wildcard.ts`

A pure subsequence matcher used by `allStructured` for structured permission matching (`bash:git stash pop` etc.). Recurses over `patterns`; `*` is a no-op pattern position (skips itself, consumes no item); a non-`*` pattern is consumed by some item, with subsequent matches required to come from later in the items sequence. Annotated in-place; `match` itself is opted out of verification via `//@ extern` (it constructs a `RegExp` — out of LS's verification model), and `matchSequence` is proven parametric over the resulting uninterpreted predicate.

Both directions of the subsequence theorem proven:

- **Soundness.** `matchSequence(items, patterns) === true ⟹ Matches(items, patterns)`, where `Matches` is the hand-added Dafny predicate that recursively existentially-quantifies a strictly-increasing index assignment for non-`*` patterns.
- **Completeness.** `Matches(items, patterns) ⟹ matchSequence(items, patterns) === true`.

A two-clause loop invariant carries the proof: `0 <= i <= items.length` plus `forall j < i. ¬(match(items[j], pattern) ∧ Matches(items[j+1..], rest))` ("no witness in the prefix scanned so far"). Soundness falls out from the recursive method's own ensures; completeness from the loop-exit invariant + the contrapositive of `Matches`'s non-`*` case. No proof body in `.dfy` — just the `predicate Matches` definition, ~6 lines.

## Caveats

- **`Wildcard.match` is opaque.** Both `evaluate.ts` proofs are parametric over the matcher — they hold for any total `(string, string) → boolean`. The actual regex-based implementation is out of LemmaScript's verification model (regex modeling excluded), but every theorem transfers unchanged if `Wildcard.match` is later replaced by a verifiable hand-written glob matcher.
- **`Schema.X` typings don't expand through ts-morph.** opencode uses `Schema.Struct(...)` and `Schema.Schema.Type<typeof X>` pervasively; ts-morph sees these as `Type<any>`. `subagent-permissions.ts` works around this with four `//@ declare-type` shim lines that give LemmaScript a simplified view of `Rule`, `Info`, `Ruleset`, and the input-record shape.

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

packages/opencode/src/permission/arity.ts             ← In-place, 3 ensures
packages/opencode/src/permission/arity.dfy.gen        ← Regeneratable
packages/opencode/src/permission/arity.dfy            ← Verified (with longest-match lemma added)

packages/opencode/src/agent/subagent-permissions.ts       ← In-place, 2 ensures + 4 declare-type shims
packages/opencode/src/agent/subagent-permissions.dfy.gen  ← Regeneratable
packages/opencode/src/agent/subagent-permissions.dfy      ← Verified (with 10-line manual proof addition)

packages/opencode/src/permission/index.ts             ← In-place, //@ verify on disabled (2 shims, 3 ensures, 3 invariants)
packages/opencode/src/permission/index.dfy.gen        ← Regeneratable
packages/opencode/src/permission/index.dfy            ← Verified (with one inline assert hint)

packages/opencode/src/util/wildcard.ts                ← In-place, //@ verify on matchSequence + //@ extern on match
packages/opencode/src/util/wildcard.dfy.gen           ← Regeneratable
packages/opencode/src/util/wildcard.dfy               ← Verified (with hand-added Matches predicate)
```

## Notes for LemmaScript

The case study drove these additions to LemmaScript itself:

**Toolchain features:**
- **Auto-extern for cross-file calls.** When `lsc` sees `Wildcard.match(a, b)` and ts-morph resolves the callee to another `.ts` file, an opaque `function {:axiom} Wildcard_match(...)` is emitted and call sites are rewritten. No annotation required; the `import` statement is the entire signal. Both namespaced (`X.y`) and bare-name (`foo`) imports are auto-resolved; `.d.ts` declarations are skipped.
- **Cross-file spec lifting.** `//@ requires` / `//@ ensures` on a cross-file callee's declaration are copied onto the axiom in the calling file's output, so callers reason against the source's verified contract. Transitive through nested cross-file references.
- **`Array.prototype.findLast`** with full completeness `ensures` on the preamble (returns the rightmost matching element; characterizes the index as maximal).
- **`Array.prototype.flat`** with the `seq<seq<T>> → seq<T>` flattening preamble.
- **`Array.prototype.join(sep)`** with a recursive `SeqJoin` preamble.
- **`//@ declare-type Name = TsType` alias form**, companion to the existing record form.
- **Dotted user-type lookup with last-segment fallback.** `Agent.Info` and `Permission.Ruleset` resolve to declare-types named `Info` / `Ruleset` via the trailing identifier.
- **Alias expansion for structural targets.** Aliases pointing to array/map/set/optional/user types are expanded at use sites; primitive-targeted aliases (`type TaskId = number`) stay nominal.
- **Module-level constants in scope for function bodies.** A top-level `const X = ...` is added to each function's environment so `X[k]` resolves to a typed map subscript rather than `unknown`.
- **C-style `for (let i = N; cond; i++/i--/i += k)` loops** desugared to `while` at extract time; counter is treated as mutable; pre/postfix `++`/`--` and `+=`/`-=` rewritten to assignments.
- **Map literals from typed record literals.** `const X: Record<string, V> = { a: 1, b: 2 }` emits as Dafny's flat `map[a := 1, b := 2]` (the chained-`set` form trips Dafny's type resolver on large dictionaries — the `ARITY` 160-entry case study forced this).
- **JS-safe `Array.prototype.slice(lo, hi)`** via a `SafeSlice` preamble that clamps both bounds to `[0, |s|]`, matching JS's permissive semantics instead of Dafny's strict `0 <= lo <= hi <= |s|`.
- **In-file `//@ extern` on a function declaration.** Marks a same-file function as a body-less axiom (signature + any `//@ requires`/`//@ ensures` only; body skipped). Parallel to the existing auto-extern for cross-file calls, registered in the same externs map, emitted the same way (`function {:axiom} foo(...)`). Use case: `Wildcard.match` is regex-based — outside LS's verification model — but `matchSequence`'s proof needs `match` to be a deterministic-but-uninterpreted predicate. `//@ extern` on `match` gives exactly that without refactoring it into a separate file. `escapeName` is now applied to extern names so Dafny-keyword collisions (`match`) resolve consistently between declaration and call sites.
- **Array destructuring with rest at let-statement level.** `const [a, , c, ...rest] = arr` desugars to individual bindings: `var a := arr[0]; var c := arr[2]; var rest := arr[3..]`. Omitted slots (`,,`) skip; rest emits as a `slice`. Single-eval temp introduced if the initializer isn't a bare variable. Nested binding patterns throw a clear error — extend when a case study hits them.
- **Brownfield `//@ verify` extraction on Effect-heavy files.** `permission/index.ts` carries a `Layer.effect(Effect.gen ...)` service, schema decls, and runtime constants that `lsc` can't model. Marking a single function with `//@ verify` makes lsc extract only that function, skipping everything else with warnings. Two narrow fixes made this work for `disabled`: (a) rewriting `if (X) continue; rest` to `if (!X) { rest }` in for-of bodies — and the post-narrow `match`/Some/None form where `continue` lands in the None arm — so Dafny's while-with-bottom-increment doesn't infinite-loop; (b) scoping auto-extern registration to function-body extraction, so module-level constants like `Event = { Asked: BusEvent.define(...) }` don't pollute the output with un-Dafny-parseable externs. Both fixes are conservative — they cover the patterns `disabled` produces, not the general continue/extern problem.

**Bug fixes uncovered along the way:**
- **Record literal emission was field-position-order, not struct-order.** `{ action: "ask", permission, pattern: "*" }` was emitting as `Rule("ask", permission, "*")` against a `Rule(permission, pattern, action)` declaration — silently misassigning all three fields. Exposed by `evaluate.ts`'s `None`-branch default.
- **`\result` narrowing through `==>` premises** wasn't firing because `\result` is `kind: "result"` in raw IR, not `kind: "var"`.
- **Quantifier left-operand parens in binop emission.** `forall i :: A || B` parses as `forall i :: (A || B)` in Dafny — the body extends as far as possible. The emitter now wraps quantifier-typed left operands in binops.
- **`inferLambdaParamTypes` not applied in `optChain` call steps.** A lambda buried inside `obj?.filter(r => ...)` got `int`-typed params instead of the array's element type.

**Pending:**
- **Schema-aware extraction.** Would remove the need for `//@ declare-type` shims when upstream types are Schema-derived. ~200–300 LOC; not strictly necessary given the shim workaround.
