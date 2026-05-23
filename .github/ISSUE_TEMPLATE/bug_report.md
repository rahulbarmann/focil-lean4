---
name: Bug report
about: Report something incorrect or unclear in the formalization
labels: bug
---

## Summary

A one-line summary of the issue.

## Where

Which file(s) and theorem(s) are affected? Link to specific
lines if possible.

## Expected behaviour

What did you expect? What does the spec, FINDINGS.md, or the
docstring lead you to expect?

## Actual behaviour

What does the code actually do or say?

## To reproduce

If applicable, the smallest set of commands or Lean snippets
that surfaces the issue. For axiom-related concerns, save a
file like `Audit.lean` containing:

```lean
import FocilLean4
#print axioms Focil.<theorem-name>
```

and run:

```bash
lake env lean Audit.lean
```

## Additional context

Any cross-references to FINDINGS.md, EIP-7805, or
consensus-specs that bear on this.
