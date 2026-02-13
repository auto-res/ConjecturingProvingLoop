

theorem interior_subset_closure_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X) : Set X) ⊆ closure (A : Set X) := by
  intro x hxInt
  have hxA : x ∈ (A : Set X) := interior_subset hxInt
  exact subset_closure hxA