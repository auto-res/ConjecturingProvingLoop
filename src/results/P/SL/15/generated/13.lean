

theorem interior_closure_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P1 (X := X) (A := interior (closure A)) h_open