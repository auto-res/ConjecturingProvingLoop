

theorem closure_compl_diff_interior_compl_eq_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (Aᶜ) \ interior (Aᶜ) = frontier (A : Set X) := by
  calc
    closure (Aᶜ) \ interior (Aᶜ)
        = frontier (Aᶜ) := by
          simpa using
            (frontier_eq_closure_diff_interior (X := X) (A := Aᶜ)).symm
    _ = frontier (A : Set X) := by
          simpa using
            (frontier_compl_eq_frontier (X := X) (A := A))