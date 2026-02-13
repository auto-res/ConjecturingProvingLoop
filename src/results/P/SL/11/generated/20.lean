

theorem interior_closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) :
    interior (closure A) = interior (closure (interior A)) := by
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) h
  simpa [hEq]