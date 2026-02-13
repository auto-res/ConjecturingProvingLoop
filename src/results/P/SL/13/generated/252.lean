

theorem Topology.closure_eq_compl_interior_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) = (interior (Aᶜ : Set X))ᶜ := by
  -- Start with `interior (Aᶜ) = (closure A)ᶜ` and take complements.
  have h : interior ((Aᶜ : Set X)) = (closure (A : Set X))ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  simpa [compl_compl] using (congrArg Set.compl h).symm