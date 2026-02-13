

theorem Topology.P1_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact (Topology.IsOpen_P1_and_P3 (A := interior (closure A)) hOpen).1