

theorem Topology.interior_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ closure B) :
    interior A ⊆ closure B := by
  intro x hxInt
  have hxA : x ∈ A := interior_subset hxInt
  exact hAB hxA