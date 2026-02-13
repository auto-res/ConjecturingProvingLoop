

theorem boundary_univ_empty {X : Type*} [TopologicalSpace X] :
    closure (Set.univ : Set X) \ interior (Set.univ : Set X) = (∅ : Set X) := by
  simp [closure_univ, interior_univ]