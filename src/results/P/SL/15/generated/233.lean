

theorem denseInterior_iff_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ interior (closure (interior A)) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    exact
      interior_closure_interior_eq_univ_of_dense
        (X := X) (A := A) hDense
  · intro hIntEq
    -- From `interior (closure (interior A)) = univ` we deduce
    -- `closure (interior A) = univ`, hence density.
    have h_closure_eq : closure (interior A : Set X) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro x _
        trivial
      · have h_sub : (Set.univ : Set X) ⊆ closure (interior A) := by
          have : (Set.univ : Set X) = interior (closure (interior A)) := by
            simpa [hIntEq]
          simpa [this] using interior_subset
        exact h_sub
    exact
      (dense_iff_closure_eq (s := interior A)).2 h_closure_eq