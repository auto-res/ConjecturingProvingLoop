

theorem interior_nonempty_imp_interiorClosure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : (interior A).Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hInt with ⟨x, hx⟩
  have hIncl : interior A ⊆ interior (closure A) :=
    interior_subset_interiorClosure (X := X) (A := A)
  exact ⟨x, hIncl hx⟩