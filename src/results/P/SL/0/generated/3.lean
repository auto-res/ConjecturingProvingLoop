

theorem interior_has_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  -- We want `interior A ⊆ interior (closure (interior (interior A)))`.
  -- Since `interior (interior A) = interior A`, this is the same as
  -- `interior A ⊆ interior (closure (interior A))`, which follows from
  -- `interior_mono` applied to `subset_closure`.
  have h : interior A ⊆ interior (closure (interior A)) := by
    have h' : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono subset_closure
    simpa [interior_interior] using h'
  simpa [interior_interior] using h