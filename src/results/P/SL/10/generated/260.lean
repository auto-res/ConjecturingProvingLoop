

theorem Topology.boundary_union_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    ((closure A \ interior A) ∪ interior A) = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxbound => exact hxbound.1
    | inr hxInt   => exact subset_closure (interior_subset hxInt)
  · intro hxCl
    classical
    by_cases hxInt : x ∈ interior A
    · exact Or.inr hxInt
    · exact Or.inl ⟨hxCl, hxInt⟩