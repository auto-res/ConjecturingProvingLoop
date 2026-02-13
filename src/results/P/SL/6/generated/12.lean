

theorem interior_closure_satisfies_P2 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  simpa using (Topology.open_satisfies_P2 (A := interior (closure A)) hOpen)