

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (A ∪ B ∪ C) := by
  -- Combine `A` and `B`
  have hAB : P3 (A ∪ B) := P3_union hA hB
  -- Combine the previous union with `C`
  have hABC : P3 ((A ∪ B) ∪ C) := P3_union hAB hC
  simpa [Set.union_assoc] using hABC