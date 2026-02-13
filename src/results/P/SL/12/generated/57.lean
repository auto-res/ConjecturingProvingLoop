

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- We will show that `closure (interior A)` is contained in
  -- `closure (interior (closure (interior A)))`.
  have h_sub :
      closure (interior A : Set X) ⊆
        closure (interior (closure (interior A))) := by
    -- First, `interior A ⊆ interior (closure (interior A))`.
    have h₁ :
        (interior A : Set X) ⊆ interior (closure (interior A)) := by
      simpa [interior_interior] using
        (Topology.interior_subset_interior_closure
          (X := X) (A := interior A))
    -- Taking closures preserves this inclusion.
    exact closure_mono h₁
  exact h_sub hx