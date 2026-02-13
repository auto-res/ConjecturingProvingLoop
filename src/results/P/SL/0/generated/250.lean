

theorem closure_union_interiors_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∪ interior (B : Set X)) ⊆
      closure (interior (A ∪ B : Set X)) := by
  -- `interior A ∪ interior B` is contained in `interior (A ∪ B)` by a previously proved lemma.
  have hSub :
      ((interior (A : Set X)) ∪ interior (B : Set X) : Set X) ⊆
        interior (A ∪ B : Set X) :=
    union_interiors_subset_interior_union (X := X) (A := A) (B := B)
  -- Taking closures preserves inclusions.
  exact closure_mono hSub