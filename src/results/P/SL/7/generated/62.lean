

theorem Topology.interiorClosureInterior_eq_interiorClosure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    interior (closure (interior A)) = interior (closure A) := by
  -- From `P1` we obtain the equality of closures
  have hEq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
  -- Applying `interior` to both sides yields the desired equality
  have hInt : interior (closure A) = interior (closure (interior A)) :=
    congrArg interior hEq
  simpa using hInt.symm