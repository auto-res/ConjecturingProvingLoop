

theorem interior_closure_interior_inter_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (A : Set X))) ∩ interior (closure (A : Set X)) =
      interior (closure (interior (A : Set X))) := by
  -- First, note that `interior (closure (interior A)) ⊆ interior (closure A)`.
  have hsubset :
      interior (closure (interior (A : Set X))) ⊆ interior (closure (A : Set X)) :=
    interior_closure_interior_subset_interior_closure (X := X) (A := A)
  -- Now prove the desired set equality by double inclusion.
  ext x
  constructor
  · -- The left‐to‐right inclusion is immediate.
    intro hx
    exact hx.1
  · -- For the converse, use the inclusion `hsubset`.
    intro hx
    exact ⟨hx, hsubset hx⟩