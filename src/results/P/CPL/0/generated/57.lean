

theorem P2_unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, P2 (s i)) → P2 (⋃ i, s i) := by
  exact P2_iUnion