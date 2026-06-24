

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P3 (A := A) := by
  dsimp [Topology.P2, Topology.P3] at h ⊢
  have hc : closure (interior A) ⊆ closure A := by
    exact closure_mono (interior_subset : interior A ⊆ A)
  have h_mono : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hc
  exact subset_trans h h_mono