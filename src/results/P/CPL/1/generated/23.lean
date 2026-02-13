

theorem P1_union_compl {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (A ∪ Aᶜ) := by
  simpa [Set.union_compl_self] using (P1_univ (X := X))