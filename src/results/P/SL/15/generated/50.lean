

theorem interior_closure_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h₁ :
        interior (closure (interior (closure A))) ⊆
          interior (closure (closure A)) :=
      interior_closure_interior_subset_interior_closure
        (X := X) (A := closure A)
    simpa [closure_closure] using h₁
  ·
    have h₂ :
        interior (closure A) ⊆
          interior (closure (interior (closure A))) :=
      interior_subset_interior_closure_interior
        (X := X) (A := closure A)
    simpa using h₂