

theorem Topology.P1_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure (interior (A : Set X))) := by
  dsimp [Topology.P1]
  intro x hx
  -- First, we show that `interior A ⊆ interior (closure (interior A))`.
  have h_int_subset : interior (A : Set X) ⊆ interior (closure (interior A)) := by
    -- Use monotonicity of `interior` on the inclusion `interior A ⊆ closure (interior A)`.
    have h : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    have : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono h
    simpa [interior_interior] using this
  -- Taking closures preserves the inclusion.
  have h_closure :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono h_int_subset
  exact h_closure hx