

theorem Topology.isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 (X := X) A := by
  dsimp [Topology.P2]
  intro x hxA
  -- First, rewrite `hxA` as a membership in `interior A`
  have hxInt : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  -- Show that `interior A` is contained in `interior (closure (interior A))`
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    have : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono subset_closure
    simpa [interior_interior] using this
  -- Conclude that `x ∈ interior (closure (interior A))`
  exact h_subset hxInt