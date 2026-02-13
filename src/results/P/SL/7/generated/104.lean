

theorem Topology.P1_closureInteriorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure A))) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior (closure A)` is contained in `interior (closure (interior (closure A)))`
  have h_subset :
      (interior (closure A) : Set X) ⊆
        interior (closure (interior (closure A))) := by
    simpa using
      (Topology.interior_subset_interiorClosureInterior (A := closure A))
  -- Taking closures preserves the inclusion
  have h_closure :
      closure (interior (closure A)) ⊆
        closure (interior (closure (interior (closure A)))) :=
    closure_mono h_subset
  exact h_closure hx