/-
  FocilLean4.lean

  Library root for the FOCIL (EIP-7805) Lean 4 formalization.
  Importing this single module pulls in:

  - `Focil.Types`: data model.
  - `Focil.Protocol`: compliance predicates.
  - `Focil.ForkChoice`: fork-choice abstraction and cornerstone
    lemma.
  - `Focil.Helpers`: auxiliary lemmas.
  - `Focil.Safety`: main theorem and corollary.

  See README.md for the project overview, FINDINGS.md for the
  research log, and CONTRIBUTING.md for build instructions.
-/

import Focil.Types
import Focil.Protocol
import Focil.ForkChoice
import Focil.Helpers
import Focil.Safety
