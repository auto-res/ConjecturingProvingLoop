

theorem Topology.P1_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior A` is open and contained in its closure
  have h_subset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    exact interior_maximal (subset_closure) isOpen_interior
  -- Taking closures preserves the inclusion
  have h_closure :
      closure (interior A) ⊆ closure (interior (closure (interior A))) := by
    exact closure_mono h_subset
  exact h_closure hx