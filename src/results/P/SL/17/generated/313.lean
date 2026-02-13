

theorem Topology.closure_frontier_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) :
    closure (frontier A) ⊆ closure (interior A) := by
  -- First, use the existing lemma that the frontier of `A`
  -- is contained in `closure (interior A)` under `P1 A`.
  have h_subset : frontier A ⊆ closure (interior A) :=
    Topology.frontier_subset_closure_interior_of_P1 (A := A) hP1
  -- Taking closures preserves inclusions; simplify `closure (closure _)`.
  simpa [closure_closure] using closure_mono h_subset