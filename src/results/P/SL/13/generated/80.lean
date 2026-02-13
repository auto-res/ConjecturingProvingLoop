

theorem Topology.closure_interior_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ⊆ closure (interior (closure A)) := by
  -- First, note that `A ⊆ closure A`.
  have h_subset : (A : Set X) ⊆ closure A := subset_closure
  -- Applying `interior` (which is monotone) to this inclusion yields
  -- `interior A ⊆ interior (closure A)`.
  have h_interior : interior (A : Set X) ⊆ interior (closure A) :=
    interior_mono h_subset
  -- Finally, taking `closure` (also monotone) on both sides gives the desired result.
  exact closure_mono h_interior