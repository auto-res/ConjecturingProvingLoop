

theorem Topology.closure_frontier_subset_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier A) ⊆ closure (Aᶜ) := by
  -- First, use the established inclusion for the frontier itself.
  have hSub : (frontier A : Set X) ⊆ closure (Aᶜ) :=
    Topology.frontier_subset_closure_compl (A := A)
  -- Taking closures preserves set inclusion.
  have hClos : closure (frontier A) ⊆ closure (closure (Aᶜ)) :=
    closure_mono hSub
  -- Simplify the double closure on the right.
  simpa [closure_closure] using hClos