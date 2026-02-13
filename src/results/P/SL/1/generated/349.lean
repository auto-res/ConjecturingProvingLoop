

theorem Topology.interior_eq_empty_of_interior_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = (∅ : Set X)) :
    interior A = (∅ : Set X) := by
  -- `interior A` is always contained in `interior (closure A)`.
  have hsubset : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A)
  -- Rewrite with the assumption `h` to obtain the desired inclusion.
  have hsubset' : interior A ⊆ (∅ : Set X) := by
    simpa [h] using hsubset
  -- The reverse inclusion `∅ ⊆ interior A` is automatic.
  exact Set.Subset.antisymm hsubset' (Set.empty_subset _)