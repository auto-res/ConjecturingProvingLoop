

theorem P3_and_interiors_equal_implies_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) →
      interior (closure (A : Set X)) = interior (closure (interior A)) →
      Topology.P2 A := by
  intro hP3 hEq
  dsimp [Topology.P2] at *
  intro x hxA
  have hxInt : x ∈ interior (closure (A : Set X)) := hP3 hxA
  simpa [hEq] using hxInt