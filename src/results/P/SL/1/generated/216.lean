

theorem Topology.P3_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (closure A) → Topology.P3 (closure B) → Topology.P3 (closure A ∪ closure B) := by
  intro hA hB
  simpa using (Topology.P3_union (A := closure A) (B := closure B) hA hB)