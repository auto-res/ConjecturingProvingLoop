

theorem P2_Union_inf {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} : (∀ i, P2 (F i)) → P2 (⋃ i, F i) := by
  intro h
  simpa using (P2_iSup_family (X := X) (F := F) h)