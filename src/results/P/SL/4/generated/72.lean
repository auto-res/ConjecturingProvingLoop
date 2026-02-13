

theorem closure_interior_union_subset_closure_interior_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `interior A ⊆ interior (A ∪ B)` by monotonicity of `interior`.
      have h_int_subset :
          interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Taking closures preserves the inclusion.
      have h_closure_subset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      exact h_closure_subset hA
  | inr hB =>
      -- Symmetric case for `B`.
      have h_int_subset :
          interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have h_closure_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      exact h_closure_subset hB