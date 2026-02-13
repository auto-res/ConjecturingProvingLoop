

theorem frontier_eq_closure_inter_compl_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    frontier (A : Set X) = closure A ∩ (interior A)ᶜ := by
  simpa [Set.diff_eq] using
    (frontier_eq_closure_diff_interior (X := X) (A := A))