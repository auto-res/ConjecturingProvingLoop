

theorem Topology.interiorClosureInterior_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  -- Obtain a point in `interior A` from `P1` and the nonemptiness of `A`.
  have hIntA : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (A := A) hP1 hA
  -- `interior A` is contained in `interior (closure (interior A))`.
  have hIncl : interior A ⊆ interior (closure (interior A)) :=
    Topology.interior_subset_interiorClosureInterior (A := A)
  -- Transport the point along the inclusion.
  rcases hIntA with ⟨x, hx⟩
  exact ⟨x, hIncl hx⟩