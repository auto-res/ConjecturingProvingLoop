

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P1 (A := A) := by
  dsimp [Topology.P2, Topology.P1] at h ⊢
  intro x hxA
  exact interior_subset (h hxA)