-- This module serves as the root of the `JordanDiagram` library: the formalization of
-- *Symmetries of Jordan Algebra Diagrams over Varying Base Rings*, built on the `Jordan` library.

-- Symmetries of a single, already-formalized Jordan algebra (no diagrams).
import JordanDiagram.Algebra.Automorphism
import JordanDiagram.Algebra.BaseChange
import JordanDiagram.Algebra.Equiv
import JordanDiagram.Algebra.Functor
import JordanDiagram.Algebra.Generation
import JordanDiagram.Algebra.Orthogonal
import JordanDiagram.Algebra.SpinFactor
import JordanDiagram.Algebra.Tower

-- General constructions missing from Mathlib (candidates for upstreaming).
import JordanDiagram.MathlibMissing.LieRingCat
import JordanDiagram.MathlibMissing.PiLie

-- The diagram layer: terminally pointed diagrams and their symmetry groups.
import JordanDiagram.Diagram.BaseChange
import JordanDiagram.Diagram.Basic
import JordanDiagram.Diagram.Derivation
import JordanDiagram.Diagram.Finiteness
import JordanDiagram.Diagram.Functor
import JordanDiagram.Diagram.Group
import JordanDiagram.Diagram.Iso
import JordanDiagram.Diagram.SpinFactor
import JordanDiagram.Diagram.Wedge
