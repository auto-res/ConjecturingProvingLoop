

theorem compl_closure_compl_eq_interior {α : Type*} [TopologicalSpace α] {s : Set α} :
    (closure (sᶜ))ᶜ = interior s := by
  have h := closure_compl_eq_compl_interior (α := α) (s := s)
  simpa [Set.compl_compl] using congrArg Set.compl h