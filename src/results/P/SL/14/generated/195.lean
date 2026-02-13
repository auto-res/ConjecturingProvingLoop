

theorem Topology.P1_iff_P2_of_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using
    (Topology.P1_iff_P2_of_isOpen (X := X) (A := interior A) hOpen)