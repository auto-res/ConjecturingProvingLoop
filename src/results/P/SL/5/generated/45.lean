

theorem interior_eq_empty_of_interior_closure_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : interior (closure (A : Set X)) = (∅ : Set X)) :
    interior (A : Set X) = (∅ : Set X) := by
  have hsub : interior (A : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    have hx' : x ∈ interior (closure (A : Set X)) :=
      (interior_subset_interior_closure (X := X) (A := A)) hx
    simpa [h] using hx'
  exact le_antisymm hsub (Set.empty_subset _)