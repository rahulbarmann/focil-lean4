/-
  Focil/Helpers.lean

  Auxiliary definitions and reusable lemmas. Right now this file is
  small; it exists as a designated home for general-purpose facts
  that grow alongside the formalisation, so the protocol and
  fork-choice files stay focused on their own concerns.
-/

import Focil.Types
import Focil.Protocol

namespace Focil

/--
  Plain unfolding of `CompliantWith` at a single transaction.

  Stating this as a named lemma rather than inlining the
  unfolding makes downstream proofs read more naturally.
-/
theorem compliantWith_imp
    {canAppend : Transaction → Block → Prop}
    {full : Block → Prop} {b : Block} {il : InclusionList}
    {tx : Transaction}
    (h : CompliantWith canAppend full b il)
    (htx : tx ∈ il.transactions) :
    tx ∈ b.transactions ∨ ¬ canAppend tx b ∨ full b :=
  h tx htx

/--
  A convenience predicate combining "this IL is in the store" and
  "this IL is considered (i.e. its author is not an equivocator)".

  Several theorems consume both facts together. Bundling them
  documents the fact that they are jointly the precondition for
  an IL to constrain a block under FOCIL.
-/
def StoredHonestly (state : FocilState) (il : InclusionList) : Prop :=
  il ∈ state.stored_ils ∧ IsConsidered state il

end Focil
