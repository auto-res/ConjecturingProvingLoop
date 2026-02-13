

theorem Topology.P3_union_three {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 C →
      Topology.P3 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First combine `A` and `B`
  have hAB : Topology.P3 (A ∪ B) := Topology.P3_union hA hB
  -- Then unite the result with `C`
  have hABC : Topology.P3 ((A ∪ B) ∪ C) := Topology.P3_union hAB hC
  -- Reassociate unions to match the desired form
  simpa [Set.union_assoc] using hABC