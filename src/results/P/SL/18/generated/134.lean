

theorem P1_iff_closure_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure (A : Set X) ⊆ closure (interior A) := by
  constructor
  · intro hP1
    exact Topology.closure_subset_closure_interior_of_P1 (A := A) hP1
  · intro hSub
    dsimp [Topology.P1] at *
    intro x hxA
    have hxCl : x ∈ closure (A : Set X) := subset_closure hxA
    exact hSub hxCl