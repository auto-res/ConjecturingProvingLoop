

theorem Topology.boundary_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ interior A = closure (Aᶜ) \ interior (Aᶜ) := by
  classical
  have h₁ : closure (Aᶜ) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  have h₂ : interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  simpa [Set.diff_eq, h₁, h₂, Set.inter_comm, Set.compl_compl]