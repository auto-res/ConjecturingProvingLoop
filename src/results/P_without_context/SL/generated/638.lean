

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 A := by
  intro h
  dsimp [Topology.P2, Topology.P3] at h ⊢
  intro x hx
  exact (interior_mono (closure_mono interior_subset)) (h hx)