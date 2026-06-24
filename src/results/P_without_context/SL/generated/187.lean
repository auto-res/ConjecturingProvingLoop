

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 (X := X) A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at hP2 ⊢
  intro x hxA
  have hx2 : x ∈ interior (closure (interior A)) := hP2 hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hsubset hx2