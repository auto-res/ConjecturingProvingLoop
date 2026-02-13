

theorem interior_union_closure_complement_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  classical
  have h : closure (Aᶜ : Set X) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (α := X) (s := A)
  calc
    interior A ∪ closure (Aᶜ)
        = interior A ∪ (interior A)ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa using Set.union_compl_self (interior A)