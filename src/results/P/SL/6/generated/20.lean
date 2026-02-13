

theorem P3_closure_interior_iff_open_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 (closure (interior (A : Set X))) ↔ IsOpen (closure (interior A)) := by
  simpa using
    (Topology.P3_closure_iff_open_closure (A := interior A))