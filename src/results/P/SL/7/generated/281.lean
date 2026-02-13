

theorem Topology.IsOpen_P1_P2_P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  simpa using (Topology.IsOpen_P1_P2_P3 (A := A ∪ B) hOpen)