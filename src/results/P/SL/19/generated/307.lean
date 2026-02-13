

theorem Topology.P1_of_frontier_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = (∅ : Set X) → Topology.P1 (A := A) := by
  intro hFrontier
  -- Since `frontier A = ∅`, it is trivially included in any set.
  have hSub : frontier A ⊆ closure (interior A) := by
    intro x hx
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hFrontier] using hx
    cases this
  -- Use the characterization of `P1` via the frontier.
  exact
    (Topology.P1_iff_frontier_subset_closure_interior
      (X := X) (A := A)).2 hSub