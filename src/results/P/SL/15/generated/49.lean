

theorem dense_union_has_P3 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense A → Topology.P3 (A ∪ B) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  have h_closureA : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  have h_subset : (Set.univ : Set X) ⊆ closure (A ∪ B) := by
    have : closure A ⊆ closure (A ∪ B) := by
      have h_sub : A ⊆ A ∪ B := Set.subset_union_left
      exact closure_mono h_sub
    simpa [h_closureA] using this
  have h_closure_union : closure (A ∪ B) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _; exact Set.mem_univ y
    · exact h_subset
  simpa [h_closure_union, interior_univ] using Set.mem_univ x