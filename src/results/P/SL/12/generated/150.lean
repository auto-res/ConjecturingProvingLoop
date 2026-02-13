

theorem Topology.interior_eq_empty_of_interior_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = (∅ : Set X)) :
    interior (A : Set X) = (∅ : Set X) := by
  -- `interior A` is always contained in `interior (closure A)`.
  have hsubset : (interior (A : Set X)) ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (X := X) (A := A)
  -- Hence, by the hypothesis, `interior A` is contained in `∅`.
  have hsubset' : (interior (A : Set X)) ⊆ (∅ : Set X) := by
    simpa [h] using hsubset
  -- Conclude the desired equality by antisymmetry.
  apply Set.Subset.antisymm hsubset'
  intro x hx; cases hx