

theorem Topology.P2_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (closure A) → Topology.P2 (closure B) → Topology.P2 (closure A ∪ closure B) := by
  intro hA hB
  simpa using (Topology.P2_union (A := closure A) (B := closure B) hA hB)