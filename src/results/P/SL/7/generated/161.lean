

theorem Topology.interior_subset_interiorClosureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior (closure A))) := by
  intro x hx
  -- Step 1: `x` belongs to `interior (closure A)`.
  have hx₁ : x ∈ interior (closure A) :=
    (Topology.interior_subset_interiorClosure (A := A)) hx
  -- Step 2: use the inclusion for `closure A`.
  have hIncl :
      interior (closure A) ⊆ interior (closure (interior (closure A))) :=
    Topology.interior_subset_interiorClosureInterior (A := closure A)
  exact hIncl hx₁