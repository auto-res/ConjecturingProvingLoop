

theorem interior_inter_closure_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ closure (Aᶜ) = (∅ : Set X) := by
  have h : closure (Aᶜ) = (interior A)ᶜ := by
    simpa using closure_compl_eq_compl_interior (α := X) (s := A)
  calc
    interior A ∩ closure (Aᶜ)
        = interior A ∩ (interior A)ᶜ := by
          simpa [h]
    _ = (∅ : Set X) := by
          simpa using Set.inter_compl_self (interior A)