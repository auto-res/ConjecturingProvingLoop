

theorem P1_implies_P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (interior A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  have hxA : (x : X) ∈ (A : Set X) := interior_subset hx
  have : x ∈ closure (interior A) := hP1 hxA
  simpa [interior_interior] using this