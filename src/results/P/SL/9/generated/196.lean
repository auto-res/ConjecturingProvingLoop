

theorem Topology.union_interiors_eq_compl_boundary {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ∪ interior (Aᶜ) = (closure A \ interior A)ᶜ := by
  classical
  -- Express `interior (Aᶜ)` in terms of `closure A`.
  have hIntComp : interior (Aᶜ : Set X) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (A := A)
  -- Rewrite the complement of the boundary and simplify.
  simpa [hIntComp, Set.diff_eq, Set.compl_inter, Set.compl_compl,
        Set.union_comm, Set.union_left_comm, Set.union_assoc]