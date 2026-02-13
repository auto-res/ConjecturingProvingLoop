

theorem interior_closure_inter_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ∩ closure (interior A) ⊆ closure A := by
  intro x hx
  -- The first component places `x` in `interior (closure A)`.
  have hInt : x ∈ interior (closure (A : Set X)) := hx.1
  -- The interior of any set is contained in the set itself.
  have hIncl : interior (closure (A : Set X)) ⊆ closure A :=
    interior_subset
  -- Conclude the desired membership.
  exact hIncl hInt