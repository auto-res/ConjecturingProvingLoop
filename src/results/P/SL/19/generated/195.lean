

theorem Topology.closure_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (closure (interior A)) ⊆ closure A := by
  -- First, eliminate the redundant double closure.
  have h_eq : closure (closure (interior A)) = closure (interior A) := by
    simpa [closure_closure]
  -- Then use the already known inclusion for a single closure of the interior.
  have h_sub : closure (interior A) ⊆ closure A :=
    Topology.closure_interior_subset_closure (A := A)
  simpa [h_eq] using h_sub