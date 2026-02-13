

theorem interior_closure_interior_subset_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (A : Set X))) ⊆
      interior (closure (A : Set X)) := by
  apply interior_mono
  exact closure_mono (interior_subset (s := A))