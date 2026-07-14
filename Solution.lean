/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.KernelReduction
import TH.CapstoneM4
import TH.GapDichotomy
import CITED.SubspaceTheorem

/-!
# The comparator solution: the real development

The counterpart of `Challenge.lean`.  Where the challenge *states* the two certified
theorems (against Mathlib alone, with `sorry` proofs), this file simply **imports the
actual proofs**, so that the constants

* `TH.superlinear_of_kernel`   (proved in `TH.KernelReduction`)
* `TH.superlinear_of_middleBand`   (proved in `TH.CapstoneM4`)
* `TH.kernel_holds`, `TH.complexity_superlinear`   (proved in `TH.GapDichotomy`)
* `Subspace.evertseSchlickewei`   (the cited axiom, declared in `CITED.SubspaceTheorem`)

are present in this module's environment with their genuine proofs and their genuine
definitional dependencies.  Comparator exports both environments and compares them; see
`Challenge.lean` for what that buys you, and `lake test` to run it.

There is deliberately no content here.  Anything proved *in this file* would be outside
the scope of what comparator checks against the challenge, so the file must stay a pure
re-export of the development.
-/
