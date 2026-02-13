

theorem interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    interior (closure (A : Set X)) ⊆ closure (interior A) := by
  -- `interior (closure A)` is contained in `closure A`.
  have hIntSub : interior (closure (A : Set X)) ⊆ closure A :=
    interior_subset
  -- `closure A` is contained in `closure (interior A)` by `P1`.
  have hClosSub : closure (A : Set X) ⊆ closure (interior A) :=
    Topology.closure_subset_closure_interior_of_P1 (A := A) hP1
  -- Combine the two inclusions.
  exact Set.Subset.trans hIntSub hClosSub