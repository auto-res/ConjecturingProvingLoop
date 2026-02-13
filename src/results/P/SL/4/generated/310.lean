

theorem interior_frontier_eq_empty_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    interior (frontier (A : Set X)) = (∅ : Set X) := by
  -- The complement of an open set is closed.
  have hClosed : IsClosed (Aᶜ) := hA.isClosed_compl
  -- For a closed set, the interior of its frontier is empty.
  have h₁ : interior (frontier (Aᶜ)) = (∅ : Set X) :=
    interior_frontier_eq_empty_of_closed (A := Aᶜ) hClosed
  -- The frontier is invariant under taking complements.
  have h₂ : frontier (Aᶜ) = frontier (A : Set X) :=
    frontier_compl_eq_frontier (A := A)
  -- Rewrite using `h₂` and conclude.
  simpa [h₂] using h₁