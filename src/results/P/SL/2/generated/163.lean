

theorem Topology.P3_closure_interior_iff_isOpen_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  simpa using
    (Topology.P3_closure_iff_isOpen_closure (A := interior A))