{-# OPTIONS --safe --without-K #-}

-- Algebras
open import HeytingAlgebras

-- Upper-set structures
open import USet.Base
open import USet.Cover
open import USet.Localized
open import USet.Mon.CM.Cover
open import USet.Box.CKBox.Cover
open import USet.Lax.SL.Cover
open import USet.Lax.PLL.Cover
open import USet.Lax.PLL.Relational
open import USet.Lattice.Localized
open import USet.Positive.Localized

-- Boilerplate for proof systems/calculi
open import Context

-- IPL ("Intuitionistic Propositional Logic")
open import Instances.IPL.System
open import Instances.IPL.Semantics.Interpretation
open import Instances.IPL.Semantics.Soundness
open import Instances.IPL.Semantics.Completeness
open import Instances.IPL.Semantics.NbE

-------------------------------
-- Constructive Modal Logics --
-------------------------------

-- CM ("Minimal constructive modal logic")
open import Instances.CM.System
open import Instances.CM.Semantics.Interpretation
open import Instances.CM.Semantics.Soundness
open import Instances.CM.Semantics.Completeness
open import Instances.CM.Semantics.NbE

-- CKBox ("Box-only Constructive K logic")
open import Instances.CKBox.System
open import Instances.CKBox.Semantics.Interpretation
open import Instances.CKBox.Semantics.Soundness
open import Instances.CKBox.Semantics.Completeness
open import Instances.CKBox.Semantics.NbE

-- SL ("Minimal lax logic with axiom S")
open import Instances.SL.System
open import Instances.SL.Semantics.Interpretation
open import Instances.SL.Semantics.Soundness
open import Instances.SL.Semantics.Completeness
open import Instances.SL.Semantics.NbE

-- PLL ("Propositional Lax Logic")
open import Instances.PLL.System
open import Instances.PLL.Semantics.Interpretation
open import Instances.PLL.Semantics.Soundness
open import Instances.PLL.Semantics.Completeness
open import Instances.PLL.Semantics.NbE

-----------------------------
-- Non-Distributive Logics --
-----------------------------

-- LatLog ("Lattice Logic")
open import Instances.LatLog.System
open import Instances.LatLog.Semantics.Interpretation
open import Instances.LatLog.Semantics.Soundness
open import Instances.LatLog.Semantics.Completeness
--open import Instances.LatLog.Semantics.NbE

-- PosLog ("Positive Logic")
open import Instances.PosLog.System
open import Instances.PosLog.Semantics.Interpretation
open import Instances.PosLog.Semantics.Soundness
open import Instances.PosLog.Semantics.Completeness
--open import Instances.PosLog.Semantics.NbE

--------------------------
-- Programming examples --
--------------------------

open import Instances.Maybe
open import Instances.Err
