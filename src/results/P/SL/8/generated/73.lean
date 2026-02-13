

theorem interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h :=
      interior_closure_interior_subset_interior_closure
        (X := X) (A := closure A)
    simpa using h
  ·
    have h_subset :
        interior (closure A) ⊆ closure (interior (closure A)) :=
      subset_closure
    have h := interior_mono h_subset
    simpa [interior_interior] using h