import { Wildcard } from "@/util/wildcard"

type Rule = {
  permission: string
  pattern: string
  action: "allow" | "deny" | "ask"
}

export function evaluate(permission: string, pattern: string, ...rulesets: Rule[][]): Rule {
  //@ ensures implies(forall((i: nat) => implies(i < rulesets.flat().length, !(Wildcard.match(permission, rulesets.flat()[i].permission) && Wildcard.match(pattern, rulesets.flat()[i].pattern)))), $result.permission === permission && $result.pattern === "*" && $result.action === "ask")
  //@ ensures implies(exists((j: nat) => j < rulesets.flat().length && Wildcard.match(permission, rulesets.flat()[j].permission) && Wildcard.match(pattern, rulesets.flat()[j].pattern)), exists((k: nat) => k < rulesets.flat().length && $result === rulesets.flat()[k] && Wildcard.match(permission, $result.permission) && Wildcard.match(pattern, $result.pattern) && forall((m: nat) => implies(k < m && m < rulesets.flat().length, !(Wildcard.match(permission, rulesets.flat()[m].permission) && Wildcard.match(pattern, rulesets.flat()[m].pattern))))))
  const rules = rulesets.flat()
  const match = rules.findLast(
    (rule) => Wildcard.match(permission, rule.permission) && Wildcard.match(pattern, rule.pattern),
  )
  return match ?? { action: "ask", permission, pattern: "*" }
}
