

theorem Topology.P1_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (closure A) → Topology.P1 (closure B) → Topology.P1 (closure A ∪ closure B) := by
  intro hA hB
  simpa using (Topology.P1_union (A := closure A) (B := closure B) hA hB)