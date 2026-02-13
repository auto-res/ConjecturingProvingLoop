

theorem Topology.closureInterior_inter_interiorClosureInterior_eq_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ interior (closure (interior A)) =
      interior (closure (interior A)) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨interior_subset hx, hx⟩