

theorem Topology.interior_subset_interior_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ interior (closure (interior A)) := by
  -- Apply monotonicity of `interior` to the inclusion
  -- `interior A ⊆ closure (interior A)`.
  have h :
      interior (interior (A : Set X)) ⊆ interior (closure (interior A)) :=
    interior_mono (subset_closure : (interior (A : Set X)) ⊆ closure (interior A))
  simpa [interior_interior] using h