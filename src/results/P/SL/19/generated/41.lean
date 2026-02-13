

theorem Topology.interior_closure_interior_closure_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h :=
      Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure A)
    simpa [closure_closure] using h
  ·
    have hSub :
        interior (closure A) ⊆ interior (closure (interior (closure A))) := by
      have h1 : (interior (closure A) : Set X) ⊆ closure (interior (closure A)) :=
        subset_closure
      have h2 : IsOpen (interior (closure A)) := isOpen_interior
      exact interior_maximal h1 h2
    intro x hx
    exact hSub hx