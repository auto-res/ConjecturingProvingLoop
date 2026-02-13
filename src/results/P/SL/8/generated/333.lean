

theorem closure_eq_compl_interior_compl {α : Type*} [TopologicalSpace α] {s : Set α} :
    closure s = (interior (sᶜ))ᶜ := by
  have h : interior (sᶜ) = (closure s)ᶜ :=
    interior_compl_eq_compl_closure (X := α) (A := s)
  calc
    closure s = ((closure s)ᶜ)ᶜ := by
      simpa using (Set.compl_compl (closure s))
    _ = (interior (sᶜ))ᶜ := by
      simpa [h]