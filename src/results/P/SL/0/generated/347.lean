

theorem closure_interior_closure_nonempty_iff_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior (closure (A : Set X)))).Nonempty ↔
      (interior (closure (A : Set X))).Nonempty := by
  simpa using
    (Topology.closure_nonempty_iff
      (X := X)
      (A := interior (closure (A : Set X))))