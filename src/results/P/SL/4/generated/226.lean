

theorem interior_union_closure_compl_eq_univ {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  have h : closure (Aᶜ) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (A := A)
  calc
    interior A ∪ closure (Aᶜ)
        = interior A ∪ (interior A)ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := Set.union_compl_self (interior A)