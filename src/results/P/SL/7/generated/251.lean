

theorem Topology.P3_subset_interiorClosureInteriorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → A ⊆ interior (closure (interior (closure A))) := by
  intro hP3 x hxA
  -- From `P3` we have that `x` belongs to `interior (closure A)`.
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  -- `interior (closure A)` is contained in `interior (closure (interior (closure A)))`.
  have hIncl :
      interior (closure A) ⊆
        interior (closure (interior (closure A))) :=
    Topology.interior_subset_interiorClosureInterior (A := closure A)
  exact hIncl hxInt