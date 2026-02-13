

theorem Topology.P1_iff_closure_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    exact closure_minimal hP1 isClosed_closure
  · intro h_subset
    dsimp [Topology.P1]
    intro x hxA
    have : x ∈ closure A := subset_closure hxA
    exact h_subset this