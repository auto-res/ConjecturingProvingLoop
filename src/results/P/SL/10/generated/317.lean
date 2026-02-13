

theorem Topology.isOpen_union_interior_compl_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : IsOpen (interior A ∪ (closure A)ᶜ) := by
  -- First, identify the set with the complement of the (closed) boundary.
  have h_eq :
      interior A ∪ (closure A)ᶜ =
        (closure A \ interior A)ᶜ := by
    simpa using
      (Topology.compl_boundary_eq_union_interior_compl_closure
        (X := X) (A := A)).symm
  -- The boundary `closure A \ interior A` is closed.
  have h_closed : IsClosed (closure A \ interior A) :=
    Topology.isClosed_closure_diff_interior (X := X) (A := A)
  -- Hence its complement is open.
  have h_open : IsOpen ((closure A \ interior A)ᶜ) :=
    h_closed.isOpen_compl
  simpa [h_eq] using h_open