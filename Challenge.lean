module

public import JordanCheck.Challenge
public import JordanDiagramCheck.Challenge

/-!
# Challenge (aggregate)

The challenge module named in `comparator.json`: it collects the trusted statements of
`JordanCheck/Challenge.lean` (the `Jordan` library) and `JordanDiagramCheck/Challenge.lean`
(the `JordanDiagram` library), so that a single `lake comparator` run checks both.
-/
