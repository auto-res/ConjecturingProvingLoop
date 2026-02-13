

theorem closure_union_interior_self {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure ((A : Set X) ∪ interior A) = closure (A : Set X) := by
  have h : (interior A : Set X) ⊆ A := interior_subset
  have hUnion : (A : Set X) ∪ interior A = A :=
    Set.union_eq_self_of_subset_right h
  simpa [hUnion]