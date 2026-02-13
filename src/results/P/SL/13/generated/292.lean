

theorem Topology.boundary_compl_eq_boundary {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure ((A : Set X)ᶜ) \ interior (Aᶜ) = closure (A : Set X) \ interior A := by
  -- Express `closure (Aᶜ)` and `interior (Aᶜ)` via complements.
  have h₁ : closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  have h₂ : interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  -- Substitute and simplify.
  simp [h₁, h₂, Set.diff_eq, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc]