

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P3 (A := A) := by
  unfold Topology.P2 at h
  unfold Topology.P3
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono interior_subset
  exact hsubset hx'