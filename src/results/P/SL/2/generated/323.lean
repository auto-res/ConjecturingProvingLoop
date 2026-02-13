

theorem Topology.isOpen_union_implies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen A → IsOpen B →
      (Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B)) := by
  intro hOpenA hOpenB
  have hOpenUnion : IsOpen (A ∪ B : Set X) := hOpenA.union hOpenB
  exact Topology.isOpen_implies_P1_P2_P3 (A := A ∪ B) hOpenUnion