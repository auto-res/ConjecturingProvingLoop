

theorem P3_empty_iff_P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) ↔ Topology.P2 (∅ : Set X) := by
  have hOpen : IsOpen (∅ : Set X) := isOpen_empty
  simpa using
    (Topology.P3_iff_P2_of_isOpen (A := (∅ : Set X)) hOpen)