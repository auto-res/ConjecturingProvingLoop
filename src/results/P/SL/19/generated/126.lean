

theorem Topology.P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A := A) ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using this
  · intro hSub
    dsimp [Topology.P1]
    intro x hxA
    have hxClos : x ∈ closure A := subset_closure hxA
    exact hSub hxClos