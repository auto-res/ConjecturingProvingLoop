

theorem Topology.P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P1 (A := A) := by
  unfold Topology.P2 at h
  unfold Topology.P1
  intro x hxA
  have : x ∈ interior (closure (interior A)) := h hxA
  exact interior_subset this