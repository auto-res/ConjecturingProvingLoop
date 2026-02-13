

theorem Topology.P2_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P2 A := by
  intro h_closure
  dsimp [Topology.P2]
  intro x hxA
  -- Since `closure (interior A) = univ`, its interior is also `univ`.
  have h_int : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [h_closure, interior_univ]
  -- Any point of `A` (indeed, any point at all) lies in this interior.
  have : (x : X) ∈ interior (closure (interior A)) := by
    simpa [h_int] using (by
      have : (x : X) ∈ (Set.univ : Set X) := by
        simp
      exact this)
  exact this