

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P3 (A := A) := by
  intro hA
  unfold Topology.P2 at hA
  unfold Topology.P3
  have hclosure : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have hinterior : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hclosure
  exact hA.trans hinterior