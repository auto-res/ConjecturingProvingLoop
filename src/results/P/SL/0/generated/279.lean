

theorem subset_interior_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    (A : Set X) ⊆ interior (closure (A : Set X)) := by
  exact interior_maximal (subset_closure : (A : Set X) ⊆ closure (A : Set X)) hA