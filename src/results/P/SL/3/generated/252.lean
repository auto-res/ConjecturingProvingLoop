

theorem closure_interior_closure_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) := by
  -- Apply the generic inclusion with `A := closure A`
  have h :
      closure (interior (closure (A : Set X))) ⊆
        closure (closure (A : Set X)) :=
    closure_interior_subset_closure (A := closure (A : Set X))
  simpa [closure_closure] using h