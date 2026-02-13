

theorem Topology.interior_closure_interior_eq_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP2 : Topology.P2 A) :
    interior (closure (interior A)) = interior (closure A) := by
  -- From `P2 A` we already have the equality of closures.
  have hEq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P2 (A := A) hP2
  -- Rewriting with `hEq` yields the desired equality of interiors.
  simpa [hEq]