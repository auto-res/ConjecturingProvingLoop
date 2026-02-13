

theorem Topology.P3_of_frontier_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ interior (closure (A : Set X)) → Topology.P3 A := by
  intro hFront
  intro x hxA
  by_cases hxInt : x ∈ interior (A : Set X)
  ·
    -- Case 1: `x` already lies in `interior A`.
    have hSub :
        (interior (A : Set X) : Set X) ⊆ interior (closure (A : Set X)) := by
      have hIncl : (A : Set X) ⊆ closure (A : Set X) := subset_closure
      exact interior_mono hIncl
    exact hSub hxInt
  ·
    -- Case 2: `x` is not in `interior A`; hence it belongs to the frontier.
    have hxCl : x ∈ closure (A : Set X) := subset_closure hxA
    have hxFront : x ∈ frontier (A : Set X) := And.intro hxCl hxInt
    exact hFront hxFront