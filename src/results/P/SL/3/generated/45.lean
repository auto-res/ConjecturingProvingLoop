

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (A : Set X))) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior A` is contained in `interior (closure (interior A))`
  have h₁ :
      interior (A : Set X) ⊆ interior (closure (interior (A : Set X))) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  -- Taking closures preserves this inclusion
  have h₂ :
      closure (interior (A : Set X)) ⊆
        closure (interior (closure (interior (A : Set X)))) :=
    closure_mono h₁
  exact h₂ hx