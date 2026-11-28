module

-- This module serves as the root of the `JordanDiagram` library: the formalization of
-- *Symmetries of Jordan Algebra Diagrams over Varying Base Rings*, built on the `Jordan` library.

-- Symmetries of a single, already-formalized Jordan algebra (no diagrams).
public import JordanDiagram.Algebra.AdelicGenus
public import JordanDiagram.Algebra.Automorphism
public import JordanDiagram.Algebra.BaseChange
public import JordanDiagram.Algebra.ChainFinite
public import JordanDiagram.Algebra.DualNumber
public import JordanDiagram.Algebra.DyadicFinite
public import JordanDiagram.Algebra.Dyadic
public import JordanDiagram.Algebra.Equiv
public import JordanDiagram.Algebra.Functor
public import JordanDiagram.Algebra.FiniteSubgroupStabilizer
public import JordanDiagram.Algebra.GaloisTwist
public import JordanDiagram.Algebra.Generation
public import JordanDiagram.Algebra.HermitianTwo
public import JordanDiagram.Algebra.OctonionNorm
public import JordanDiagram.Algebra.Orthogonal
public import JordanDiagram.Algebra.OrthogonalFlag
public import JordanDiagram.Algebra.OrthogonalFlagIso
public import JordanDiagram.Algebra.SpinFactor
public import JordanDiagram.Algebra.SquareZero
public import JordanDiagram.Algebra.TwistedDescent
public import JordanDiagram.Algebra.StabilizerFinite
public import JordanDiagram.Algebra.SpinFactorFormallyReal
public import JordanDiagram.Algebra.Tower

-- General constructions missing from Mathlib (candidates for upstreaming).
public import JordanDiagram.MathlibMissing.AnisotropicBound
public import JordanDiagram.MathlibMissing.ClassSum
public import JordanDiagram.MathlibMissing.FractionRingOrder
public import JordanDiagram.MathlibMissing.GaloisDescent
public import JordanDiagram.MathlibMissing.GrothendieckCocartesian
public import JordanDiagram.MathlibMissing.LieRingCat
public import JordanDiagram.MathlibMissing.Minkowski
public import JordanDiagram.MathlibMissing.PiLie
public import JordanDiagram.MathlibMissing.PosDefIntegerPoints
public import JordanDiagram.MathlibMissing.PowerSeriesMatrix
public import JordanDiagram.MathlibMissing.PowerSeriesOrder
public import JordanDiagram.MathlibMissing.SemilinearBaseChange

-- The diagram layer: terminally pointed diagrams and their symmetry groups.
public import JordanDiagram.Diagram.BaseChange
public import JordanDiagram.Diagram.Basic
public import JordanDiagram.Diagram.Derivation
public import JordanDiagram.Diagram.DualNumber
public import JordanDiagram.Diagram.Finiteness
public import JordanDiagram.Diagram.Forms
public import JordanDiagram.Diagram.Functor
public import JordanDiagram.Diagram.Group
public import JordanDiagram.Diagram.Family
public import JordanDiagram.Diagram.Iso
public import JordanDiagram.Diagram.MaximalFinite
public import JordanDiagram.Diagram.NodePreimage
public import JordanDiagram.Diagram.Ordered
public import JordanDiagram.Diagram.OrderedPowerSeries
public import JordanDiagram.Diagram.PowerSeries
public import JordanDiagram.Diagram.Pseudofunctor
public import JordanDiagram.Diagram.Representability
public import JordanDiagram.Diagram.GroupScheme
public import JordanDiagram.Diagram.Product
public import JordanDiagram.Diagram.SpinFactor
public import JordanDiagram.Diagram.SpinFactorFinite
public import JordanDiagram.Diagram.Twisted
public import JordanDiagram.Diagram.TwistedGeneral
public import JordanDiagram.Diagram.Wedge
public import JordanDiagram.Diagram.Wreath
