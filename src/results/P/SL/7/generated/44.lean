

theorem Topology.interiorClosureInterior_eq_interiorClosure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    interior (closure (interior A)) = interior (closure A) := by
  have hClosureEq : closure (interior A) = closure A :=
    Topology.closureInterior_eq_closure_of_P2 (A := A) hP2
  simpa [hClosureEq] using
    (rfl : interior (closure (interior A)) =
      interior (closure (interior A)))