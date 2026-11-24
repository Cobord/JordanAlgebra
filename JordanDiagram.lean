module

-- This module serves as the root of the `JordanDiagram` library: the formalization of
-- *Symmetries of Jordan Algebra Diagrams over Varying Base Rings*, built on the `Jordan` library.

-- Symmetries of a single, already-formalized Jordan algebra (no diagrams).
public import JordanDiagram.Algebra.Automorphism
public import JordanDiagram.Algebra.BaseChange
public import JordanDiagram.Algebra.Equiv
public import JordanDiagram.Algebra.Functor
public import JordanDiagram.Algebra.Generation
public import JordanDiagram.Algebra.Orthogonal
public import JordanDiagram.Algebra.OrthogonalFlag
public import JordanDiagram.Algebra.OrthogonalFlagIso
public import JordanDiagram.Algebra.SpinFactor
public import JordanDiagram.Algebra.Tower

-- General constructions missing from Mathlib (candidates for upstreaming).
public import JordanDiagram.MathlibMissing.LieRingCat
public import JordanDiagram.MathlibMissing.PiLie
public import JordanDiagram.MathlibMissing.PowerSeriesMatrix

-- The diagram layer: terminally pointed diagrams and their symmetry groups.
public import JordanDiagram.Diagram.BaseChange
public import JordanDiagram.Diagram.Basic
public import JordanDiagram.Diagram.Derivation
public import JordanDiagram.Diagram.Finiteness
public import JordanDiagram.Diagram.Functor
public import JordanDiagram.Diagram.Group
public import JordanDiagram.Diagram.Iso
public import JordanDiagram.Diagram.PowerSeries
public import JordanDiagram.Diagram.Product
public import JordanDiagram.Diagram.SpinFactor
public import JordanDiagram.Diagram.Twisted
public import JordanDiagram.Diagram.Wedge
public import JordanDiagram.Diagram.Wreath
