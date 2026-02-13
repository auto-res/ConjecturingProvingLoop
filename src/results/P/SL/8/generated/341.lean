

theorem interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ∩ closure A = interior A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hxInt
    have hxCl : x ∈ closure A := subset_closure (interior_subset hxInt)
    exact And.intro hxInt hxCl