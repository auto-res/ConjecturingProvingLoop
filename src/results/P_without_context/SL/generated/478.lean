

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hA
  dsimp [Topology.P2, Topology.P3] at *
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hsubset hx'