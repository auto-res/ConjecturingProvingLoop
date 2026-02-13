

theorem Topology.closure_union_closure_subset_closure_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∪ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_subset : closure (A : Set X) ⊆ closure (A ∪ B) :=
        Topology.closure_subset_closure_union_left (X := X) (A := A) (B := B)
      exact h_subset hA
  | inr hB =>
      have h_subset : closure (B : Set X) ⊆ closure (A ∪ B) :=
        Topology.closure_subset_closure_union_right (X := X) (A := A) (B := B)
      exact h_subset hB