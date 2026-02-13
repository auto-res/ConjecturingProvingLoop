

theorem interior_closure_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa using
    Topology.isOpen_imp_P2 (X := X) (A := interior (closure A)) h_open