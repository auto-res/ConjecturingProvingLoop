

theorem open_subset_closure_implies_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hOpenU : IsOpen (U : Set X)) (hSub : U ⊆ closure (A : Set X)) :
    U ⊆ interior (closure A) := by
  exact interior_maximal hSub hOpenU