

theorem closure_union_interior_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) ⊆ closure (interior (A ∪ B)) := by
  exact
    closure_mono
      (interior_union_subset (A := A) (B := B))