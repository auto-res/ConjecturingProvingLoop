

theorem Topology.P3_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact (Topology.IsOpen_P1_and_P3 (A := interior (closure A)) hOpen).2