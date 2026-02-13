

theorem closure_eq_univ_of_interior_closure_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  · intro x _
    have hxInt : x ∈ interior (closure (A : Set X)) := by
      simpa [h] using Set.mem_univ x
    exact (interior_subset : interior (closure (A : Set X)) ⊆ closure (A : Set X)) hxInt