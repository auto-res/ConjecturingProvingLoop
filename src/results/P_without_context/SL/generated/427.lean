

theorem Topology.P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro h
  dsimp [Topology.P1, Topology.P2]
  intro x hx
  have : x ∈ interior (closure (interior A)) := h hx
  exact interior_subset this