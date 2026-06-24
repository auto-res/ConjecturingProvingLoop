

theorem P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P1] at *
  intro x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have hxCl : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ _) hxInt
  exact hxCl