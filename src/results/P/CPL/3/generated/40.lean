

theorem P3_Union_dense {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, closure (s i) = Set.univ) → P3 (⋃ i, s i) := by
  intro h
  apply P3_iUnion
  intro i
  exact P3_of_dense (h i)