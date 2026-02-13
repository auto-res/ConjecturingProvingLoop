

theorem closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ⊆
      closure (interior (closure (A : Set X))) := by
  apply closure_mono
  exact interior_subset_interior_closure (A := A)