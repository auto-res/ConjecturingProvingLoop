

theorem Topology.P1_of_closureInterior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior A) = A) : Topology.P1 (A := A) := by
  dsimp [Topology.P1]
  intro x hxA
  have : x ∈ closure (interior A) := by
    simpa [h] using hxA
  exact this