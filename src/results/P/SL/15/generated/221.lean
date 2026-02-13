

theorem closure_subset_closure_interior_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ interior (closure B)) :
    closure A ⊆ closure (interior (closure B)) := by
  exact closure_mono hAB