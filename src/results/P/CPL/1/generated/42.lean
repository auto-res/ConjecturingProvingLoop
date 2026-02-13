

theorem P2_Union_finset {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 (⋃ i, A i) := by
  simpa using P2_unionᵢ (A := A) h