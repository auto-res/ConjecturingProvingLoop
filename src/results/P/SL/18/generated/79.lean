

theorem P123_union_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  have hOpenUnion : IsOpen (A ∪ B : Set X) := hA.union hB
  exact Topology.P123_of_open hOpenUnion