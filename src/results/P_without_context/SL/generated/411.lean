

theorem Topology.P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P1]
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset (s := closure (interior A))
  exact h_subset hx_int