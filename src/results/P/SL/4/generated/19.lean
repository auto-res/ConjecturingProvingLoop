

theorem union_interior_closure_subset_interior_closure_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  rcases hx with hxA | hxB
  · -- Case: `x ∈ interior (closure A)`
    have hA : closure A ⊆ closure (A ∪ B) :=
      closure_mono (Set.subset_union_left)
    have hA_int : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
      interior_mono hA
    exact hA_int hxA
  · -- Case: `x ∈ interior (closure B)`
    have hB : closure B ⊆ closure (A ∪ B) :=
      closure_mono (Set.subset_union_right)
    have hB_int : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
      interior_mono hB
    exact hB_int hxB