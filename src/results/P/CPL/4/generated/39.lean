

theorem P1_iff_frontier_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ frontier A ⊆ closure (interior A) := by
  classical
  constructor
  · intro hP1
    exact P1_frontier_subset (A := A) hP1
  · intro hFront
    dsimp [Topology.P1] at *
    intro x hxA
    by_cases hxInt : x ∈ interior A
    · -- `x` already lies in `interior A`
      exact subset_closure hxInt
    · -- `x` is not in `interior A`; hence it is on the frontier of `A`
      have hx_cl : x ∈ closure A := subset_closure hxA
      have hx_frontier : x ∈ frontier A := by
        -- `frontier A = closure A \ interior A`
        change x ∈ closure A \ interior A
        exact And.intro hx_cl hxInt
      exact hFront hx_frontier