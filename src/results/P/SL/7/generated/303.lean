

theorem Topology.interiorClosure_subset_closureInteriorClosureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (A : Set X)) ⊆
      closure (interior (closure (interior (closure (A : Set X))))) := by
  intro x hx
  -- First, place `x` inside `interior (closure (interior (closure A)))`
  -- using the established inclusion for `A := closure A`.
  have hxInt :
      x ∈ interior (closure (interior (closure (A : Set X)))) :=
    (Topology.interior_subset_interiorClosureInterior
        (A := closure (A : Set X))) hx
  -- The interior is always contained in the closure of itself.
  exact subset_closure hxInt