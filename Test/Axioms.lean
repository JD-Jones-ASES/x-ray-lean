import Solution
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let text := name.toString
    if text.startsWith "XRay." || text.startsWith "_private.XRay." then
      count := count + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
  unless count ≥ 50 do
    throwError "Axiom audit found only {count} project declarations"
  unless env.contains ``XRay.ordinary_extension do
    throwError "The ordinary extension theorem was not imported"
  logInfo m!"Audited {count} project declarations; no unexpected axioms."
