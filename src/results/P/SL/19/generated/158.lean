

theorem Topology.P1_iff_frontier_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) ↔ frontier A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `P1` we have `closure A ⊆ closure (interior A)`.
    have hSub : closure A ⊆ closure (interior A) :=
      (Topology.closure_subset_closure_interior_of_P1 (A := A)) hP1
    -- Any point of the frontier lies in `closure A`, hence in `closure (interior A)`.
    intro x hxFrontier
    exact hSub hxFrontier.1
  · intro hFrontier
    dsimp [Topology.P1]
    intro x hxA
    by_cases hxInt : x ∈ interior A
    · -- Case `x ∈ interior A`: the claim is immediate.
      exact subset_closure hxInt
    · -- Case `x ∉ interior A`: then `x` belongs to the frontier of `A`.
      have hxFrontier : x ∈ frontier A := by
        have hxClos : x ∈ closure A := subset_closure hxA
        exact And.intro hxClos hxInt
      exact hFrontier hxFrontier