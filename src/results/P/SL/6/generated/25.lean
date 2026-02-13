

theorem P3_closure_interior_closure_iff_open_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (closure (A : Set X))))
      ↔ IsOpen (closure (interior (closure A))) := by
  simpa using
    (Topology.P3_closure_iff_open_closure
      (A := interior (closure (A : Set X))))