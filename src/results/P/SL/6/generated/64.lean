

theorem P1_iff_P3_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (A : Set X)) ↔ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using (Topology.P1_iff_P3_of_isOpen (A := interior A) hOpen)