

theorem P2_Union_closed {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} : (∀ i, IsClosed (A i)) → (∀ i, P2 (A i)) → P2 (⋃ i, A i) := by
  intro _ hP2
  simpa using (P2_unionᵢ (A := A) hP2)