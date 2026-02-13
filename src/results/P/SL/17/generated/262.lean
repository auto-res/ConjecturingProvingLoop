

theorem Topology.frontier_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (interior A) ⊆ closure A := by
  intro x hx
  -- First, upgrade the membership to `frontier A` using the existing lemma.
  have hFrontA : x ∈ frontier A :=
    (Topology.frontier_interior_subset_frontier (A := A)) hx
  -- Points in the frontier of `A` lie in `closure A`.
  exact hFrontA.1