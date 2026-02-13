

theorem Topology.interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h :=
      Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure A)
    simpa [closure_closure] using h
  ·
    have h_subset : interior (closure A) ⊆ closure (interior (closure A)) := by
      intro x hx
      exact subset_closure hx
    have h_open : IsOpen (interior (closure A)) := isOpen_interior
    have h := interior_maximal h_subset h_open
    simpa using h