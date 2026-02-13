

theorem interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior A ⊆ closure (interior (closure A)) := by
  intro x hx
  -- First, enlarge `interior A` to `interior (closure A)`.
  have hx_int_closure : x ∈ interior (closure A) :=
    Topology.interior_subset_interior_closure (X := X) (A := A) hx
  -- Then, any point of an open set belongs to the closure of that set.
  exact subset_closure hx_int_closure