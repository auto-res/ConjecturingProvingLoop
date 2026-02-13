

theorem Topology.interior_diff_closure_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ closure (B : Set X) : Set X) = interior A \ closure B := by
  have h_closed : IsClosed (closure (B : Set X)) := isClosed_closure
  simpa using
    Topology.interior_diff_closed_eq (X := X) (A := A) (C := closure B) h_closed