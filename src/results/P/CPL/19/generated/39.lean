

theorem P1_union_distrib {X : Type*} [TopologicalSpace X] {A B C : Set X} : P1 (A ∪ (B ∩ C)) ↔ P1 ((A ∪ B) ∩ (A ∪ C)) := by
  simpa [Set.union_inter_distrib_left]