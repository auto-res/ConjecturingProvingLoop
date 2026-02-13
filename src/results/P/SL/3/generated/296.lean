

theorem P1_P2_P3_union_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  simpa using
    (Topology.P1_P2_P3_of_isOpen (A := (A ∪ B : Set X)) hOpen)