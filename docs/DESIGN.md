# Design notes

This document explains the _methodology_ behind the
formalization: what we modelled, what we abstracted, and why.
README.md is for users; FINDINGS.md catalogues spec-level
issues; this file is the architectural rationale.

A senior researcher reading the code without this document can
recover most of these decisions from the file-level comments
and the FINDINGS document. This page collects them in one
place.

## Table of contents

1. [Goal and scope](#1-goal-and-scope)
2. [Abstraction layering](#2-abstraction-layering)
3. [Why the safety property is structural](#3-why-the-safety-property-is-structural)
4. [The opacity of `CanAppend`](#4-the-opacity-of-canappend)
5. [Why state and fullness live on `ForkChoice`](#5-why-state-and-fullness-live-on-forkchoice)
6. [Why no Mathlib](#6-why-no-mathlib)
7. [Reading the proof end-to-end](#7-reading-the-proof-end-to-end)
8. [What this design rules out](#8-what-this-design-rules-out)

---

## 1. Goal and scope

The single property we set out to prove:

> Under FOCIL's modified fork-choice rule, an honest non-equivocating
> inclusion list whose transaction is appendable and whose target
> block has room cannot be censored: no block omitting that
> transaction can become the canonical chain head.

Notable scoping decisions made up front:

- **Safety only, not liveness.** The theorem rules out _bad
  outcomes_; it does not exhibit _good outcomes_. We do not
  prove "a compliant block exists at every slot."
- **One slot at a time.** The theorem talks about a single
  block at a single slot. Cross-slot reasoning (e.g. amortised
  censorship across many slots) is out of scope.
- **No EVM, no economics.** The protocol's safety question can
  be stated and answered without modelling the EVM or
  proof-of-stake economics. This is a strength: the result is
  agnostic to the gas model, the staking distribution, the
  slashing rules.

The Lean formalization tightens the informal English argument
that motivated EIP-7805; it does not extend its scope.

## 2. Abstraction layering

The six files in `Focil/` form a strict dependency chain:

```
Types.lean        (no dependencies)
   ↓
Protocol.lean     (depends on Types)
   ↓
ForkChoice.lean   (depends on Types, Protocol)  ←  Helpers.lean
   ↓                                                (depends on Types, Protocol)
Safety.lean       (depends on Types, Protocol, ForkChoice, Helpers)
   ↓
StakeModel.lean   (depends on all of the above)
```

Each layer has exactly one job:

- **`Types.lean`**: nouns. Validators, transactions, inclusion
  lists, blocks, fork-choice store. No verbs.
- **`Protocol.lean`**: the compliance rule. `CompliantWith`,
  `FocilCompliant`. This is the predicate an honest attester
  evaluates, lifted from the spec's `validate_inclusion_lists`.
- **`ForkChoice.lean`**: the soundness story. Bundles a store
  snapshot, a fullness model, and the two propositional
  obligations on attester voting that the safety argument
  needs. Proves the cornerstone lemma
  `canonical_implies_compliant`.
- **`Helpers.lean`**: small reusable lemmas.
- **`Safety.lean`**: the headline theorems
  (`focil_one_of_n_protection`, `focil_censorship_resistance`,
  `censoring_block_not_canonical`). Three short proofs, all
  directly atop `canonical_implies_compliant`.
- **`StakeModel.lean`**: the PoS-derived layer. Defines
  `StakeModel` and `AttesterRun`, proves the counting
  lemma, and supplies `AttesterRun.toForkChoice` together
  with the end-to-end `focil_pos_derived_safety`. Discharges
  both `ForkChoice` structural obligations from a >2/3
  honest-validator assumption.

Layering matters because each level is a _contract_ between
the layer above and the layer below. A future refinement of
`CanAppend` (Section 4) lives entirely inside `Protocol.lean`
and Safety doesn't change. A future refinement of `ForkChoice`
(Section 5) can change everything in `ForkChoice.lean` and
both the data model and the compliance rule are unaffected.

## 3. Why the safety property is structural

The proof of `focil_censorship_resistance` is short: three
substantive steps. That is by design. The intellectual content
lives in the structure, not in the tactics.

The argument:

1. **Canonicality forces compliance.** If a block is the
   canonical chain head, it has accumulated a quorum of
   attestations, and at least one attestation came from an
   honest validator (axiom `quorum_has_honest_voter`). Honest
   validators only vote for compliant blocks (axiom
   `honest_attester_compliance`). Therefore the canonical
   block is compliant against the bundled fork-choice store.

2. **Compliance forces inclusion.** Compliance unfolds
   per-transaction to a three-way disjunction: included, or
   un-appendable, or block-full. The hypotheses
   `CanAppend tx b` and `¬ full b` rule out the latter two
   disjuncts. Only inclusion remains.

3. **Done.** `tx ∈ b.transactions`.

This is not a clever proof. It is a clean one. The conceptual
work happened when designing `ForkChoice` and `FocilCompliant`
so that the chain `canonical → quorum → honest voter →
compliance → inclusion-or-excused → inclusion` follows from
two short structural lemmas. The Lean formalization makes that
shape explicit. The slogan "FOCIL's safety is a structural
consequence of canonicality relative to a fork-choice rule
that filters non-compliant blocks" is captured directly in the
proof shape.

## 4. The opacity of `CanAppend`

`CanAppend : Transaction → Block → Prop` is declared
`opaque`, with no concrete realization. The safety theorem
quantifies universally over its possible realizations.

**Why.** Modelling `CanAppend` faithfully would require an EVM
model with sender nonces, balances, gas-arithmetic, and account
abstraction interactions. None of this changes the _structure_
of the safety argument; it only fixes which transactions count
as "appendable." Decoupling the two layers:

- Lets the safety proof be checked by anyone with a stock Lean
  toolchain in seconds.
- Lets a future refinement (FINDINGS.md §4.3) plug in a real
  account-state abstraction without touching the existing
  proof.
- Makes the conditional nature of the result explicit: the
  theorem holds _modulo a faithful realization of EVM
  validity_. A reader can substitute their own threat model
  for `CanAppend` and read off what the theorem then claims.

**The trade-off.** The theorem says nothing about adversarial
construction of `CanAppend`. The Finding §2.3 attack vectors
(nonce-bump front-running, balance-drain, AA revocation) all
manifest as "the proposer constructed a `b` such that
`CanAppend tx b` is false," and the theorem then has nothing
to say. A refined `CanAppend` derived from a per-account
abstraction is the natural follow-on.

## 5. Why state and fullness live on `ForkChoice`

The structure-design decision that took the most thought.

An earlier draft of `ForkChoice` made `state : FocilState` and
`full : Block → Prop` _parameters_ of the soundness obligation
field:

```lean
honest_attester_compliance :
    ∀ (full : Block → Prop) (b : Block) (state : FocilState)
      (v : ValidatorIndex),
      IsHonest v → Voted v b →
      FocilCompliant full b state
```

This is the signature a researcher might write down naively,
treating "honest attesters refuse to vote for non-compliant
blocks" as a single global invariant.

**The signature is unsatisfiable non-vacuously.** With
`CanAppend` opaque, it cannot be discharged for any concrete
`(b, v)` pair where the antecedent is satisfiable. Sketch:
pick any transaction `tx` not in `b.transactions` and a state
whose only stored IL contains `tx`. The compliance obligation
becomes
`tx ∈ b.transactions ∨ ¬ CanAppend tx b ∨ full b`,
each disjunct of which is unprovable in general. The only
escape is to make `Voted v b` constantly false, which is exactly
what the vacuous example does.

**The fix.** Bundle `state` and `full` as fields of
`ForkChoice`. The soundness obligation now reads:

```lean
honest_attester_compliance :
    ∀ (b : Block) (v : ValidatorIndex),
      IsHonest v → Voted v b →
      FocilCompliant full b state
```

where `state` and `full` are the structure's own fields. This
matches what an honest attester actually does in real
LMD-GHOST: vote relative to _their_ fork-choice store snapshot
at attestation time, not relative to all conceivable snapshots.

The corrected formalization admits a non-vacuous concrete
instance, `threeValidatorForkChoice`, where both obligations
are discharged by genuine case analysis. See FINDINGS.md §2.7
for the full discussion.

This is the kind of subtle assumption a Lean formalization is
specifically good at surfacing. The English-prose version of
"honest attesters refuse to vote for non-compliant blocks" is
ambiguous; the Lean version forces a choice; the wrong choice
is unsatisfiable; making the right choice clarifies what the
informal claim was always supposed to mean.

## 6. Why no Mathlib

We use only the Lean core library. No Mathlib import.

Reasons:

- The safety proof needs only `List` membership and
  case-analysis on inductive constructors. Nothing in
  Mathlib's mathematical machinery is load-bearing.
- A Mathlib import inflates build times by an order of
  magnitude (small minutes vs. tens of seconds). The first
  experience a reviewer has of the repository is `lake
build`; making that fast matters.
- A Mathlib-free formalization is reproducible by anyone with
  a stock Lean toolchain. There is no "did I install the
  right Mathlib commit?" failure mode.

A future refinement that genuinely needs Mathlib (e.g. for
`Finset` arithmetic in a stake-weighted quorum model) can add
the dependency without breaking the existing proofs. We left
that door open.

## 7. Reading the proof end-to-end

The full reading order, with the architectural role of each
file:

1. **`Focil/Types.lean`**: what FOCIL _is_. Read every
   docstring. Each abstraction choice (e.g. dropping
   `inclusion_list_committee_root`) is justified inline.
2. **`Focil/Protocol.lean`**: what FOCIL _requires_. Map
   `CompliantWith` against `validate_inclusion_lists` in
   `consensus-specs/_features/eip7805/fork-choice.md`. Note
   the per-transaction independent quantification (FINDINGS.md
   §2.5).
3. **`Focil/ForkChoice.lean`**: what _attesters_ do. The two
   propositional obligations are the load-bearing assumptions
   of the safety theorem; everything else is plumbing.
4. **`Focil/Safety.lean`**: what _follows_. Two short proofs.
5. **`Tests/Examples.lean`**: the model in action. Ten
   scenarios spanning compliance rule, vacuous instance,
   non-vacuous 3-validator instance, and equivocator
   degradation.

The most subtle piece is `ForkChoice` (§5 above). If you
disagree with that abstraction, the rest of the proofs are
still correct, but they may be answering a different question
than you would have asked.

## 8. What this design rules out

To set expectations precisely:

- **The headline 1-of-N theorem captures the EIP claim, but
  the formal `Tx` and `Block` are abstract.** The theorem
  applies to one specific IL committee (existentially
  quantified over committee size); the structures it
  manipulates are minimal Lean records, not SSZ-encoded
  containers.
- **No execution semantics.** `CanAppend` is opaque
  (Section 4).
- **No timing, no gossip, no equivocator detection.** All
  three are pre-conditions on `state.stored_ils` /
  `state.equivocators`, not parts of the fork-choice rule.
  See FINDINGS.md §2.2, §2.6, §4.2.
- **No stake weighting.** The PoS layer in
  `Focil/StakeModel.lean` treats each validator as one stake
  unit. A weighted variant generalises directly but is left as
  follow-on work (see CONTRIBUTING.md §2).
- **No cross-slot reasoning.** Single block, single slot.

These are not bugs; they are the perimeter. The strength of
the formalization is that each one is a _named_ perimeter,
documented in `FINDINGS.md`, and the natural seam along which
the next contribution should grow.
