

theorem denseInterior_implies_closure_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    closure (interior (closure A)) = (Set.univ : Set X) := by
  -- `closure (interior A)` is the whole space by density.
  have h_closure_intA : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- `interior A ⊆ interior (closure A)`, hence the corresponding closures satisfy
  -- `closure (interior A) ⊆ closure (interior (closure A))`.
  have h_subset :
      (Set.univ : Set X) ⊆ closure (interior (closure A)) := by
    have h_int_subset : interior A ⊆ interior (closure A) :=
      Topology.interior_subset_interior_closure (X := X) (A := A)
    have h_closure_subset :
        (closure (interior A) : Set X) ⊆ closure (interior (closure A)) :=
      closure_mono h_int_subset
    simpa [h_closure_intA] using h_closure_subset
  -- Conclude the desired equality.
  apply Set.Subset.antisymm
  · intro x _; exact Set.mem_univ x
  · exact h_subset