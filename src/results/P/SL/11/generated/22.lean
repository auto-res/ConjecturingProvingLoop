

theorem interior_closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : Topology.P2 A) :
    interior (closure A) = interior (closure (interior A)) := by
  have hEq : closure A = closure (interior A) :=
    closure_eq_closure_interior_of_P2 (A := A) h
  simpa [hEq]