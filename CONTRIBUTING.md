# Contributing to focil-lean4

Contributions are welcome, especially from protocol researchers,
consensus-layer developers, and members of the Lean 4 community.
The project is intentionally scoped narrowly so each contribution
has clear leverage; the most impactful directions are listed in
[FINDINGS.md §5](FINDINGS.md#5-where-the-formalization-is-conditional)
and at the bottom of the [README](README.md#contributing-and-follow-on-work).

## Orientation

If you have not yet read the project documentation, the suggested
order is:

- [`README.md`](README.md) for the headline claim and quick start.
- [`docs/DESIGN.md`](docs/DESIGN.md) for the architectural rationale.
- [`docs/walkthrough.md`](docs/walkthrough.md) for a guided tour of
  the main theorem.
- [`FINDINGS.md`](FINDINGS.md) for the spec issues and model
  limitations the formalization surfaced.

## Building and checking the proofs

Install [`elan`](https://github.com/leanprover/elan):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

From the repository root:

```bash
lake build              # builds the main library (Focil/* + FocilLean4)
lake build Tests        # builds the worked-examples library
```

The toolchain is pinned in `lean-toolchain`. Lake will fetch the
right Lean version automatically. There are no external Lean
dependencies; the formalization deliberately avoids Mathlib (see
[FINDINGS.md §4.1](FINDINGS.md#41-why-no-mathlib)).

A successful `lake build` means every theorem in the library has
been kernel-checked, including all proof bodies.

## Verifying axiom-freeness

The repository's central correctness claim is that the safety
theorems depend on zero kernel axioms. To reproduce the audit:

Create a file `AuditAxioms.lean` at the repository root with:

```lean
import FocilLean4

#print axioms Focil.focil_one_of_n_protection
#print axioms Focil.focil_censorship_resistance
#print axioms Focil.censoring_block_not_canonical
#print axioms Focil.canonical_implies_compliant
#print axioms Focil.AttesterRun.toForkChoice
#print axioms Focil.focil_pos_derived_safety
#print axioms Focil.front_running_breaks_appendability
```

Run:

```bash
lake env lean AuditAxioms.lean
```

Expected output:

```
'Focil.focil_one_of_n_protection' does not depend on any axioms
'Focil.focil_censorship_resistance' does not depend on any axioms
'Focil.censoring_block_not_canonical' does not depend on any axioms
'Focil.canonical_implies_compliant' does not depend on any axioms
'Focil.AttesterRun.toForkChoice' depends on axioms: [propext, Quot.sound]
'Focil.focil_pos_derived_safety' depends on axioms: [propext, Quot.sound]
'Focil.front_running_breaks_appendability' depends on axioms: [propext, Quot.sound]
```

The four pure safety theorems depend on **zero** kernel
axioms. The PoS-derived layer and the nonce-only account-state
layer both use `propext` and `Quot.sound`, two foundational
kernel axioms that ship with every Lean installation.
`Classical.choice` and `sorryAx` are not used anywhere; if any
line lists either, that is a regression. Please file an issue.

## Concrete contribution opportunities

These are the open problems from
[FINDINGS.md §5–§6](FINDINGS.md), framed as standalone projects.
The PoS-derived `ForkChoice` instantiation has already been
done in `Focil/StakeModel.lean`; the items below are the
remaining tightenings.

### 1. Refined `CompliantWith` capturing sequential dependence (highest leverage)

EIP-7805 §"Payload Construction" notes that an IL transaction
can become valid because an earlier IL transaction was
appended. The current `CompliantWith` predicate quantifies
per-transaction independently and does not capture this. A
refined version would take the IL transactions in some order
and thread a hypothetical post-state through the appendability
check.

This is structurally invasive: `CanAppend` would need to take a
list of "tentatively appended transactions" as a parameter, and
the safety proof's case analysis would need to handle the new
shape. The high-level argument carries over.

### 2. Stake-weighted `StakeModel`

The current `StakeModel` treats each validator as one stake
unit. A weighted variant would replace
`(filter ...).length` in the supermajority condition with
`(filter ...).map weight |>.sum`. The counting argument
(`filter_count_overlap`) generalises to weighted sums in a
straightforward way. Doing this would let the formalization
reflect Ethereum's actual stake-weighted PoS without changing
the headline theorem statement.

### 3. Refined `CanAppend` covering balance and AA dimensions

The current account-state model in `Focil/AccountState.lean`
tracks nonces only and proves the front-running attack from
[FINDINGS.md §2.3](FINDINGS.md#23-adversarial-validity-changes)
as the theorem `front_running_breaks_appendability`. Two
follow-on extensions are natural:

- **Balance-aware variant.** Track per-sender balance and
  formalize the balance-drain attack. The structural shape is
  the same as the nonce model; the case analysis surface
  doubles.
- **EIP-7702-aware variant.** Add EOA delegation state and
  formalize the AA-revocation attack. Larger scope; useful as
  Hegotá's account-abstraction story stabilises.

### 4. Model `on_inclusion_list` and equivocator detection

Currently `state.equivocators` is taken as input. A faithful model
would consume a stream of `SignedInclusionList` messages and
produce the resulting `(stored_ils, equivocators)` pair, with a
proof that the construction matches the Python `on_inclusion_list`
function in `consensus-specs`.

### 5. IL gossip / network adversary model

Capture the threat surface for an adversary who can selectively
delay, drop, or duplicate IL gossip messages. The current model
abstracts this by demanding `il ∈ state.stored_ils`; a finer model
would let us reason about _which_ ILs reach the store under
adversarial network conditions.

## Coding conventions

### Lean style

- **Every `structure`, `def`, `theorem`, and `lemma` has a
  `/-- ... -/` docstring.** The docstring explains what the
  declaration represents _in protocol terms_, not just what it
  is in Lean syntax. For theorems, the docstring states the
  property in plain English and explains why it matters.
- **Significant proof steps have inline comments.** A reviewer
  reading the proof should be able to follow the argument
  without knowing every Lean tactic. Tactic-only proofs are
  acceptable for one- or two-line proofs of self-evident
  propositions.
- **No `sorry`, no `admit`, no `axiom` declarations** in any file
  under `Focil/` or `Tests/`. The whole point of the project is
  that the kernel signs off on every step.
- **No emojis** in code, comments, or string literals.
- **Snake-case for tactic-style hypotheses** (`h_il_stored`),
  camel-case for definitions (`FocilCompliant`,
  `canonical_implies_compliant` is an exception following the
  Mathlib convention for theorems-stated-as-implications).

### File structure

- One conceptual unit per file. `Focil/Types.lean` holds _only_
  data; `Focil/Protocol.lean` holds _only_ the compliance rule;
  etc. This keeps the dependency graph linear.
- Group related declarations under `-- =====` style separators
  with descriptive names where a file gets long.

### Pull-request checklist

Before submitting a PR:

- [ ] `lake build` passes.
- [ ] `lake build Tests` passes.
- [ ] The axiom-freeness audit (above) still reports zero kernel
      axioms for the listed theorems.
- [ ] `grep -rn "sorry" --include="*.lean" .` produces no output.
- [ ] New declarations carry docstrings.
- [ ] Significant proof steps carry inline comments.
- [ ] Any new abstraction or simplification is documented in
      `FINDINGS.md`.

## Where to ask questions

- **Lean 4 questions**: the [Lean Zulip](https://leanprover.zulipchat.com)
  is the most reliable place for proof-engineering help.
- **FOCIL protocol questions**: the
  [ethresear.ch FOCIL thread](https://ethresear.ch/t/fork-choice-enforced-inclusion-lists-focil-a-simple-committee-based-inclusion-list-proposal/19870)
  and the
  [EIP-7805 magicians thread](https://ethereum-magicians.org/t/eip-7805-committee-based-fork-choice-enforced-inclusion-lists-focil/21578).
- **Bug reports / discussion of the formalization**: open a
  GitHub issue on this repository.
