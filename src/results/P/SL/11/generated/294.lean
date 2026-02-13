

theorem P3_of_interior_closure_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = A) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  have : x ∈ interior (closure A) := by
    simpa [h] using hxA
  exact this