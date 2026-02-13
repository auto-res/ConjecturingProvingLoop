

theorem P2_of_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (interior A)) = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  intro x _hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h] using this