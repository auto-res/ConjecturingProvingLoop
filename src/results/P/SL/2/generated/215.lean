

theorem Topology.frontier_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (interior (A : Set X)) ⊆ closure (A : Set X) := by
  intro x hx
  -- First, use the general fact `frontier S ⊆ closure S` with `S := interior A`.
  have hx₁ : x ∈ closure (interior (A : Set X)) :=
    (Topology.frontier_subset_closure (A := interior A)) hx
  -- Next, `closure (interior A)` is contained in `closure A`.
  have hsubset : (closure (interior (A : Set X)) : Set X) ⊆ closure A :=
    Topology.closure_interior_subset_closure (A := A)
  -- Combining the two inclusions yields the desired result.
  exact hsubset hx₁