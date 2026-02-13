

theorem P3_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : P3 A) (hB : P3 B) (hC : P3 C) (hD : P3 D) : P3 (A ∪ B ∪ C ∪ D) := by
  have hABC : P3 (A ∪ B ∪ C) := P3_union_three hA hB hC
  have hABCD : P3 ((A ∪ B ∪ C) ∪ D) := P3_union hABC hD
  simpa [Set.union_assoc] using hABCD