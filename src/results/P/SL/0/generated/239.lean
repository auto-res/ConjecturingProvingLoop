

theorem union_closures_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ⊆ closure (A ∪ B : Set X) := by
  intro x hx
  cases hx with
  | inl hxA =>
      exact
        (Topology.closure_subset_closure_union_left
          (X := X) (A := A) (B := B)) hxA
  | inr hxB =>
      exact
        (Topology.closure_subset_closure_union_right
          (X := X) (A := A) (B := B)) hxB