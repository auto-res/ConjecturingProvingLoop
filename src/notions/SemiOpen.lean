import Mathlib
import Aesop

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/-- A set is semi-open if it is a subset of the closure of its interior. -/
def SemiOpen (A : Set X) : Prop :=
  A ⊆ closure (interior A)

/-- A set is alpha-open if it is a subset of the interior of the closure of its interior. -/
def AlphaOpen (A : Set X) : Prop :=
  A ⊆ interior (closure (interior A))

/-- A set is preopen if it is a subset of the interior of its closure. -/
def PreOpen (A : Set X) : Prop :=
  A ⊆ interior (closure A)
