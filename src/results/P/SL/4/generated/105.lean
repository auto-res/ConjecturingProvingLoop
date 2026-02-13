

theorem closure_interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → closure (interior (closure A)) = (Set.univ : Set X) := by
  intro hDense
  -- `closure A = univ` because `A` is dense.
  have h_closure_univ : (closure A : Set X) = Set.univ := hDense.closure_eq
  -- Hence `interior (closure A) = univ`.
  have h_int_univ : interior (closure A) = (Set.univ : Set X) := by
    have h_univ : interior (Set.univ : Set X) = (Set.univ : Set X) := by
      simpa using (isOpen_univ : IsOpen (Set.univ : Set X)).interior_eq
    simpa [h_closure_univ] using h_univ
  -- Taking closures preserves the equality, so the target closure is also `univ`.
  calc
    closure (interior (closure A))
        = closure (Set.univ : Set X) := by
          simpa [h_int_univ]
    _ = (Set.univ : Set X) := by
          simpa using closure_univ