

theorem interior_closure_P1_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) ↔ Topology.P3 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa using
    Topology.isOpen_P1_iff_P3 (X := X) (A := interior (closure A)) h_open