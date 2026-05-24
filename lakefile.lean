import Lake
open Lake DSL

/-!
  Lake build manifest for `focil-lean4`.

  Layout:
  - `FocilLean4` (default target) is the main library: the data
    model, the compliance rule, the fork-choice abstraction, and
    the safety theorems. Building this is what verifies the
    central proof claim of the project.
  - `Tests` is a separate library of worked example scenarios that
    exercise the data model. It depends on `FocilLean4` and is
    built explicitly via `lake build Tests`.

  No external dependencies. The proofs use only the Lean core
  library; Mathlib is intentionally not used (see FINDINGS.md
  §4.1 for the rationale).
-/

package «focil-lean4» where
  -- Lean compiler options applied to every module in the package.
  --   `pp.unicode.fun = true` enables the unicode arrow in
  --     pretty-printed output (purely cosmetic).
  --   `autoImplicit = false` requires every implicit argument to
  --     be declared explicitly. We prefer this for clarity in a
  --     specification project.
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib FocilLean4 where
  -- The umbrella `FocilLean4` module re-exports every `Focil.*`
  -- submodule. Listing the submodules here as roots ensures Lake
  -- compiles each one as part of the default target.
  roots := #[
    `FocilLean4,
    `Focil.Types,
    `Focil.Protocol,
    `Focil.ForkChoice,
    `Focil.Helpers,
    `Focil.Safety,
    `Focil.StakeModel,
    `Focil.AccountState
  ]

lean_lib Tests where
  -- Worked example scenarios. Kept separate from the main library
  -- so that proof checking the core does not depend on the
  -- example file. Build with `lake build Tests`.
  roots := #[`Tests.Examples]
