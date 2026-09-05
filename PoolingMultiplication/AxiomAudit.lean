import PoolingMultiplication
import Lean.Util.CollectAxioms

/-!
# Dependency audit

Audit every declaration in the project namespace, including definitions.
Fail the build if any transitive axiom is outside Lean's three standard
logical foundations. This also excludes native-computation trust extensions.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    if (`PoolingMultiplication).isPrefixOf name then
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do
          throwError "Unapproved axiom {dependency} in {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "No project declarations were audited"
  logInfo m!"Audited {checked} project declarations: only propext, Classical.choice, Quot.sound."

#print axioms PoolingMultiplication.pooling_characterization
#print axioms PoolingMultiplication.rigidity_of_comm
#print axioms PoolingMultiplication.rigidity_of_assoc
