

theorem P2_of_interior_closure_interior_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (closure (interior (A : Set X))) = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  have hx : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt] using hx