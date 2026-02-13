

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior A` is contained in `interior (closure (interior A))`
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    have : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono subset_closure
    simpa [interior_interior] using this
  -- Taking closures preserves this inclusion
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono h_subset
  exact h_closure_subset hx