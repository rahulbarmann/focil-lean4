/-
  Focil/AccountState.lean

  Concrete instantiation of EVM-validity (nonce-only) and a
  formal demonstration of the adversarial-validity attack from
  FINDINGS §2.3.

  ## What this module does

  The main safety theorems in `Focil/Safety.lean` and the
  PoS-derived theorem in `Focil/StakeModel.lean` are stated
  against an `opaque CanAppend : Transaction → Block → Prop`,
  with `h_can_append : CanAppend tx b` as a hypothesis. The
  proof is universally quantified over `CanAppend`
  realizations. This module supplies one such realization:
  a nonce-only account-state model where `tx` is appendable iff
  its nonce matches the next-expected nonce of its sender after
  the block's transactions have been applied.

  Crucially, this module does *not* replace the opaque
  `CanAppend` in the safety theorems. It is a companion
  predicate, defined alongside, that lets us state and prove
  *separate* theorems about the appendability layer. The main
  safety chain remains universally quantified.

  ## What this module formalizes

  FINDINGS §2.3 ("Adversarial validity changes") describes a
  family of attacks where a colluding party manipulates the
  account state so that an IL transaction becomes invalid right
  before block production. The simplest such attack is *nonce
  front-running*: the adversary submits a transaction sharing
  the IL transaction's `(sender, nonce)`, the proposer appends
  it to the block, and the IL transaction's nonce is now stale.

  The theorem `front_running_breaks_appendability` formalizes
  exactly this attack: given a block `b` to which an IL
  transaction `tx_il` is appendable (and an "evil" tx with the
  same sender and nonce is also appendable from `b`'s
  post-state), the extension `b ++ [tx_evil]` makes `tx_il` no
  longer appendable. The proposer can then legitimately invoke
  the conditional-inclusion exemption.

  ## What this implies for the main safety theorem

  The main `focil_pos_derived_safety` takes
  `h_can_append : CanAppend tx b` as a hypothesis. If a
  consumer instantiates `CanAppend` with `canAppendToBlock`
  from this module, the front-running attack tells us
  *exactly* when that hypothesis fails: when the proposer has
  appended a same-(sender, nonce) tx to the block. This is
  not a flaw in the safety theorem; it is a precise statement
  of the adversarial surface that lives outside it. The
  formalization makes this surface formally explicit; the EIP
  text describes it informally only.

  ## Scope (deliberately limited)

  - Only nonces are tracked. Balances, gas accounting, contract
    state, account abstraction, and EIP-7702 delegations are
    out of scope. A balance dimension would double the case
    surface and would not strengthen the §2.3 demonstration:
    the nonce dimension is sufficient to exhibit the attack.
  - Transactions that do not match the expected nonce are
    treated as no-ops on the state (they would not execute in
    a real EVM either). We do not model gas refunds, partial
    state changes, or revert semantics.
  - The `canAppendToBlock` predicate is intentionally a
    standalone definition rather than a redefinition of the
    opaque `Focil.CanAppend`. The two are unrelated by
    construction; a consumer wishing to use the nonce-only
    model with the main safety theorem would substitute
    `canAppendToBlock initial` for `CanAppend` at instance
    construction time.

  ## Axiom dependencies

  The theorems in this module use `simp` lemmas about
  `List.foldl_append` and decidable equality on `Nat`. They
  inherit `propext` and `Quot.sound`, the same standard
  kernel axioms used by `Focil.StakeModel`. No
  `Classical.choice`, no `sorryAx`.
-/

import Focil.Types

namespace Focil

-- =========================================================================
-- Account-state primitives
-- =========================================================================

/--
  A sender is identified by its EOA index. We reuse `Nat` for
  consistency with `Transaction.sender` in `Focil/Types.lean`.
-/
abbrev Sender : Type := Nat

/--
  An account state assigns each sender its next-expected nonce.
  Senders that have never transacted are at nonce 0.

  We model state as a total function rather than a partial
  map because the proofs only ever read state at concrete
  sender indices, and the function form makes the
  arithmetic-on-state lemmas trivial.
-/
abbrev AccountState : Type := Sender → Nat

/--
  The genesis account state: every sender starts at nonce 0.
-/
def AccountState.initial : AccountState := fun _ => 0

-- =========================================================================
-- The transaction-application step
-- =========================================================================

/--
  Apply a single transaction to an account state.

  If the transaction's nonce matches the current next-expected
  nonce for its sender, the sender's nonce is incremented by 1.
  Otherwise (an invalid transaction), the state is unchanged.

  This is the minimum nonce model: it captures exactly the
  EVM behaviour relevant to the adversarial-validity attack
  in FINDINGS §2.3, and nothing else.
-/
def applyTx (state : AccountState) (tx : Transaction) : AccountState :=
  fun s =>
    if s = tx.sender ∧ tx.nonce = state tx.sender then
      state s + 1
    else
      state s

/--
  The post-state of a list of transactions, starting from
  `initial` and applying each transaction in order.
-/
def postState (initial : AccountState) (txs : List Transaction) : AccountState :=
  txs.foldl applyTx initial

-- =========================================================================
-- The nonce-only appendability predicate
-- =========================================================================

/--
  A transaction is *appendable* in the nonce-only model iff its
  nonce matches the current next-expected nonce for its sender.

  This is the formal counterpart of "the EVM would accept this
  tx as the next one from this sender" under the nonce-only
  abstraction.
-/
def canAppendNonce (state : AccountState) (tx : Transaction) : Prop :=
  tx.nonce = state tx.sender

/--
  Lifted to blocks: a transaction is appendable to block `b`
  (starting from `initial` account state) iff its nonce matches
  the post-state nonce of its sender after applying all of `b`'s
  transactions.

  This is the concrete realization a consumer would substitute
  for the abstract `CanAppend` in `Focil.Protocol`. The main
  safety theorems remain universally quantified over `CanAppend`;
  this is one specific realization that lets us state separate
  theorems about the appendability layer.
-/
def canAppendToBlock (initial : AccountState) (b : Block)
    (tx : Transaction) : Prop :=
  canAppendNonce (postState initial b.transactions) tx

-- =========================================================================
-- Folding lemmas
-- =========================================================================

/--
  The post-state distributes over list concatenation: applying
  a sequence then a single more transaction is the same as
  applying that single transaction to the post-state of the
  prefix. Direct from `List.foldl_append`.
-/
theorem postState_append_singleton
    (initial : AccountState) (txs : List Transaction)
    (tx : Transaction) :
    postState initial (txs ++ [tx]) =
    applyTx (postState initial txs) tx := by
  unfold postState
  simp [List.foldl_append]

-- =========================================================================
-- The front-running attack as a theorem
-- =========================================================================

/--
  **Front-running breaks appendability (FINDINGS §2.3).**

  Given:

  - A block `b` to which an IL transaction `tx_il` is
    appendable (under the nonce-only model).
  - An "evil" transaction `tx_evil` sharing `tx_il`'s sender,
    also appendable to `b`.

  Then: the extension `b ++ [tx_evil]` makes `tx_il` no longer
  appendable.

  This formalizes the nonce-front-running attack: a colluding
  party submits a transaction with the same `(sender, nonce)`
  as an IL-listed transaction, the proposer appends it to the
  block, and the IL transaction's nonce is now stale. The
  proposer can then legitimately invoke EIP-7805's
  conditional-inclusion exemption (`¬ CanAppend tx_il b'`).

  Note that we do *not* need to explicitly assume that
  `tx_evil` and `tx_il` share a nonce: the same-sender
  hypothesis combined with both being appendable to the same
  state already forces nonce collision (both must equal the
  state's expected nonce for that sender). The hypothesis set
  is therefore minimal: same sender plus simultaneous
  appendability is sufficient to expose the attack.

  This theorem does *not* contradict the main safety theorem.
  The safety theorem takes `h_can_append` as a hypothesis;
  this theorem says "the hypothesis can be made false by an
  adversary who picks `b'` adversarially." The two theorems
  are about different layers (safety conditional on
  appendability vs. how appendability behaves under
  adversarial block construction). The attack surface they
  jointly characterize is exactly what FINDINGS §2.3
  describes.
-/
theorem front_running_breaks_appendability
    (initial : AccountState)
    (b : Block)
    (tx_il tx_evil : Transaction)
    (h_same_sender    : tx_evil.sender = tx_il.sender)
    (h_il_appendable  : canAppendToBlock initial b tx_il)
    (h_evil_appendable: canAppendToBlock initial b tx_evil) :
    ¬ canAppendToBlock initial
        { b with transactions := b.transactions ++ [tx_evil] }
        tx_il := by
  -- Goal:
  --   ¬ canAppendToBlock initial
  --       { b with transactions := b.transactions ++ [tx_evil] } tx_il
  --
  -- Unfold to:
  --   ¬ tx_il.nonce =
  --       postState initial (b.transactions ++ [tx_evil]) tx_il.sender
  --
  -- Then `postState_append_singleton` gives us:
  --   ¬ tx_il.nonce =
  --       applyTx (postState initial b.transactions) tx_evil tx_il.sender
  --
  -- Let s = postState initial b.transactions.
  -- From h_il_appendable:   tx_il.nonce   = s tx_il.sender.
  -- From h_evil_appendable: tx_evil.nonce = s tx_evil.sender.
  -- From h_same_sender + h_same_nonce + the above, the applyTx
  -- condition fires and the value at tx_il.sender becomes
  -- s tx_il.sender + 1, which differs from tx_il.nonce.
  intro h_app
  unfold canAppendToBlock canAppendNonce at h_app
  rw [show ({ b with transactions := b.transactions ++ [tx_evil] }
           : Block).transactions = b.transactions ++ [tx_evil] from rfl,
      postState_append_singleton] at h_app
  -- h_app : tx_il.nonce =
  --         applyTx (postState initial b.transactions) tx_evil tx_il.sender
  -- Unfold applyTx and use the condition's truth.
  unfold applyTx at h_app
  -- The condition for the `if` is
  --   tx_il.sender = tx_evil.sender ∧ tx_evil.nonce = s tx_evil.sender
  -- We prove both conjuncts and then rewrite via `if_pos`.
  have h_cond_left : tx_il.sender = tx_evil.sender := h_same_sender.symm
  have h_cond_right :
      tx_evil.nonce = postState initial b.transactions tx_evil.sender :=
    h_evil_appendable
  rw [if_pos ⟨h_cond_left, h_cond_right⟩] at h_app
  -- h_app : tx_il.nonce =
  --         postState initial b.transactions tx_il.sender + 1
  -- From h_il_appendable: tx_il.nonce = postState ... tx_il.sender.
  have h_il_nonce :
      tx_il.nonce = postState initial b.transactions tx_il.sender :=
    h_il_appendable
  rw [h_il_nonce] at h_app
  -- h_app : postState ... tx_il.sender = postState ... tx_il.sender + 1
  -- Contradiction via Nat.succ_ne_self.
  exact Nat.succ_ne_self _ h_app.symm

end Focil
