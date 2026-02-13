

theorem denseInterior_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  -- First, rewrite the target set using the density hypothesis.
  have h_int :
      interior (closure (interior A)) = (Set.univ : Set X) := by
    have : interior (closure (interior A)) =
        interior (Set.univ : Set X) := by
      simpa [h_dense]
    simpa [interior_univ] using this
  -- Now the inclusion `A ⊆ interior (closure (interior A))` is immediate.
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_int] using this