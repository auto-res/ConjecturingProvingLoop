

theorem Topology.interior_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  -- The set `interior A` is contained in its closure.
  have hsubset : (interior A : Set X) ⊆ closure (interior A) := by
    intro x hx
    exact subset_closure hx
  -- Apply the monotonicity of `interior`.
  have hmono : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono hsubset
  simpa [interior_interior] using hmono