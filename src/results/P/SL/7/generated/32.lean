

theorem Topology.P2_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact (IsOpen_P2 (A := interior (closure A)) hOpen)