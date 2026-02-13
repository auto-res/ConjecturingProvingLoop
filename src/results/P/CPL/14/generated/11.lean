

theorem P2_iUnion {X I} [TopologicalSpace X] {F : I → Set X} (h : ∀ i, P2 (F i)) : P2 (⋃ i, F i) := by
  simpa using P2_bUnion (F := F) h