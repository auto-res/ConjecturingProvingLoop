

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior A` is open and contained in `closure (interior A)`,
  -- hence it is contained in the *interior* of that closure.
  have h_sub : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    have h_subset : (interior A : Set X) ⊆ closure (interior A) := by
      intro y hy
      exact subset_closure hy
    exact interior_maximal h_subset isOpen_interior
  -- Taking closures preserves inclusions.
  have h_closure :
      (closure (interior A) : Set X) ⊆
        closure (interior (closure (interior A))) :=
    closure_mono h_sub
  exact h_closure hx