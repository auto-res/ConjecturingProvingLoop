

theorem P1_subset_closureInteriorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    A ⊆ closure (interior (closure (interior A))) := by
  -- Expand the definition of `P1` to obtain the starting inclusion.
  dsimp [Topology.P1] at hP1
  intro x hxA
  have hxClInt : x ∈ closure (interior A) := hP1 hxA
  -- Use monotonicity to enlarge the ambient set.
  have h_subset :
      closure (interior A) ⊆ closure (interior (closure (interior A))) := by
    simpa [interior_interior] using
      closure_interior_subset_closure_interior_closure
        (X := X) (A := interior A)
  exact h_subset hxClInt