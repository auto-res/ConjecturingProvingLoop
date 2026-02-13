

theorem closure_interior_closure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (closure A) ∪ interior (closure B)) ⊆
      closure (interior (closure (A ∪ B))) := by
  have hSub :
      interior (closure A) ∪ interior (closure B) ⊆
        interior (closure (A ∪ B)) :=
    interior_closure_union_subset (A := A) (B := B)
  exact closure_mono hSub