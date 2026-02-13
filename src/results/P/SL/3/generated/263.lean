

theorem P1_P2_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  have hOpen : IsOpen (∅ : Set X) := isOpen_empty
  simpa using
    (Topology.P1_P2_P3_of_isOpen (A := (∅ : Set X)) hOpen)