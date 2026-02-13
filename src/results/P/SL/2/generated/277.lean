

theorem Topology.dense_right_implies_P3_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Dense (B : Set X) → Topology.P3 (A ∪ B) := by
  intro hDense
  intro x hxUnion
  -- `closure B = univ` because `B` is dense.
  have hClB : closure (B : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence `closure (A ∪ B)` is also the whole space.
  have hClUnion : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _; simp
    · intro y _
      -- Since `closure B = univ`, any point lies in `closure B`.
      have hy : (y : X) ∈ closure (B : Set X) := by
        simpa [hClB]
      -- `B ⊆ A ∪ B`, and closure is monotone.
      have : (closure (B : Set X) : Set X) ⊆ closure (A ∪ B : Set X) := by
        have hSub : (B : Set X) ⊆ A ∪ B := by
          intro z hz; exact Or.inr hz
        exact closure_mono hSub
      exact this hy
  -- Since `closure (A ∪ B) = univ`, its interior is also `univ`.
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hClUnion, interior_univ] using this