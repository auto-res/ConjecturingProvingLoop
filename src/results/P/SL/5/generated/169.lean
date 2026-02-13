

theorem P1_of_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior (A : Set X)) = A) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x hxA
  have : x ∈ closure (interior (A : Set X)) := by
    have : x ∈ (A : Set X) := hxA
    simpa [h] using this
  exact this