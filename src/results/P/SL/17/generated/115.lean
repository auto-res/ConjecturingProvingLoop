

theorem Topology.interior_closure_interior_eq_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    interior (closure (interior A)) = interior (closure A) := by
  -- From `P1 A` we have the equality of closures.
  have hEq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (A := A) hP1
  -- Rewriting with `hEq` yields the desired equality of interiors.
  simpa [hEq]