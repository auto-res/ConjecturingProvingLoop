

theorem Topology.P1_iff_closure_subset_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ closure (A : Set X) ⊆ closure (interior A) := by
  unfold Topology.P1
  constructor
  · intro hP1
    have h : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hP1
    simpa [closure_closure] using h
  · intro hSub
    intro x hxA
    have hx_closureA : x ∈ closure (A : Set X) := subset_closure hxA
    exact hSub hx_closureA