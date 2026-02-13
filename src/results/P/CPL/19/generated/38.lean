

theorem P2_countable_union {X : Type*} [TopologicalSpace X] {F : ℕ → Set X} : (∀ n, P2 (F n)) → P2 (⋃ n, F n) := by
  intro h
  simpa using (P2_iSup_family (X := X) (F := F) h)