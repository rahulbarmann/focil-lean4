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
  - `Focil.StakeModel`: PoS-derived `ForkChoice` instantiation
    discharging the soundness obligations from a >2/3 honest
    validator assumption.
  - `Focil.AccountState`: nonce-only EVM-validity model;
    formalizes the adversarial-validity attack from
    FINDINGS §2.3 as a theorem.
  - `Focil.EndToEnd`: end-to-end safety theorems against a
    concrete EVM-validity model. Pins the validity predicate
    to the nonce proxy from `Focil.AccountState`; lifts the
    last opacity from the safety chain.

  See README.md for the project overview, FINDINGS.md for the
  research log, and CONTRIBUTING.md for build instructions.
-/

import Focil.Types
import Focil.Protocol
import Focil.ForkChoice
import Focil.Helpers
import Focil.Safety
import Focil.StakeModel
import Focil.AccountState
import Focil.EndToEnd
