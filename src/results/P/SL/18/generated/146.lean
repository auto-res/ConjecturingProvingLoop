

theorem P1_of_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h] using this