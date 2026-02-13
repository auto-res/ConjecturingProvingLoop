

theorem Topology.interior_closure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A : Set X)) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_subset : closure (A : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      have h_int_subset :
          interior (closure (A : Set X)) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_subset
      exact h_int_subset hA
  | inr hB =>
      have h_subset : closure (B : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have h_int_subset :
          interior (closure (B : Set X)) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_subset
      exact h_int_subset hB