

theorem closure_union_interior_complement_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A ∪ interior (Aᶜ) = (Set.univ : Set X) := by
  have h : interior (Aᶜ : Set X) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (X := X) (A := A)
  calc
    closure A ∪ interior (Aᶜ)
        = closure A ∪ (closure A)ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa using Set.union_compl_self (closure A)