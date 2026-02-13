

theorem Topology.dense_interior_union_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : Dense (interior A)) : Dense (interior (A ∪ B)) := by
  -- From density obtain the closure equality for `interior A`.
  have hClosureA : closure (interior A) = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- `interior A` is contained in `interior (A ∪ B)`.
  have hSubsetInt : interior A ⊆ interior (A ∪ B) := by
    apply interior_mono
    intro x hx
    exact Or.inl hx
  -- Therefore the corresponding closures satisfy the same inclusion.
  have hSubsetCl :
      closure (interior A) ⊆ closure (interior (A ∪ B)) :=
    closure_mono hSubsetInt
  -- Combine with `hClosureA` to see that the latter closure is the whole space.
  have hEq : closure (interior (A ∪ B)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; simp
    · simpa [hClosureA] using hSubsetCl
  -- Conclude density from the closure equality.
  exact (dense_iff_closure_eq).2 hEq