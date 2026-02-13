

theorem Topology.P2_iff_P3_of_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) ↔ Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  simpa using (Topology.P2_iff_P3_of_isOpen (A := interior (closure A)) hOpen)