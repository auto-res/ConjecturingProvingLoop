

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P1] at *
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hP2 hx
  have hsub : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact hsub hx'