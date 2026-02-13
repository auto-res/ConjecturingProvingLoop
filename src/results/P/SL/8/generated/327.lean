

theorem closure_compl_eq_compl_interior {α : Type*} [TopologicalSpace α]
    {s : Set α} :
    closure (sᶜ) = (interior s)ᶜ := by
  classical
  -- First, apply the known relation to the complement `sᶜ`.
  have h : interior s = (closure (sᶜ))ᶜ := by
    simpa [Set.compl_compl s] using
      (interior_compl_eq_compl_closure (A := sᶜ))
  -- Taking complements of both sides yields the desired equality.
  have : closure (sᶜ) = (interior s)ᶜ := by
    have h' := congrArg Set.compl h
    simpa [Set.compl_compl] using h'
  simpa using this