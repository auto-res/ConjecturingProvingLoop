

theorem interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure A := by
  intro x hxInt
  have hxA : x ∈ (A : Set X) := interior_subset hxInt
  exact (subset_closure : (A : Set X) ⊆ closure A) hxA