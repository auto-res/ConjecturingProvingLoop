

theorem interior_closure_eq_interior_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    interior (closure A) = interior (closure (interior A)) := by
  have hClosEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 hP1
  simpa [hClosEq] using
    (rfl : interior (closure A) = interior (closure A))