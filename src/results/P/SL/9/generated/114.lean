

theorem Topology.interior_subset_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  intro x hx
  have h_incl : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    -- `interior A` is open and contained in `closure (interior A)`,
    -- hence it is contained in the interior of that closure.
    have h_subset : (interior A : Set X) ⊆ closure (interior A) := by
      intro y hy
      exact subset_closure hy
    exact interior_maximal h_subset isOpen_interior
  exact h_incl hx