
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

-- Boilerplate for systems
open import Context

-- IPL
open import Instances.IPL.System
open import Instances.IPL.Semantics.Interpretation
open import Instances.IPL.Semantics.Soundness
open import Instances.IPL.Semantics.Completeness
open import Instances.IPL.Semantics.NbE

-- CM
open import Instances.CM.System
open import Instances.CM.Semantics.Interpretation
open import Instances.CM.Semantics.Soundness
open import Instances.CM.Semantics.Completeness
open import Instances.CM.Semantics.NbE

-- CKBox
open import Instances.CKBox.System
open import Instances.CKBox.Semantics.Interpretation
open import Instances.CKBox.Semantics.Soundness
--open import Instances.CKBox.Semantics.Completeness
open import Instances.CKBox.Semantics.NbE

-- SL
open import Instances.SL.System
open import Instances.SL.Semantics.Interpretation
open import Instances.SL.Semantics.Soundness
open import Instances.SL.Semantics.Completeness
open import Instances.SL.Semantics.NbE

-- PLL
open import Instances.PLL.System
open import Instances.PLL.Semantics.Interpretation
open import Instances.PLL.Semantics.Soundness
open import Instances.PLL.Semantics.Completeness
open import Instances.PLL.Semantics.NbE

-- Lambda calculi with monads
open import Instances.Maybe
open import Instances.Err
