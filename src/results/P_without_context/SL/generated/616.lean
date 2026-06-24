

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) A) : Topology.P3 (X := X) A := by
  unfold Topology.P2 at h
  unfold Topology.P3
  intro x hxA
  have hxInt : x ∈ interior (closure (interior A)) := h hxA
  have hSub : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hSub hxInt