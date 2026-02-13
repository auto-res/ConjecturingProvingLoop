

theorem Topology.interiorClosureCompl_eq_compl_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (Aᶜ)) = (closure (interior A))ᶜ := by
  have h₁ : closure (Aᶜ) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (A := A)
  have h₂ : interior ((interior A)ᶜ) = (closure (interior A))ᶜ :=
    Topology.interior_compl_eq_compl_closure (A := interior A)
  simpa [h₁] using h₂