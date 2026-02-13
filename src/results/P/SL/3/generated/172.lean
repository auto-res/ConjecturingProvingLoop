

theorem closure_eq_interior_union_closure_diff_interior {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) =
      interior (A : Set X) ∪ (closure (A : Set X) \ interior (A : Set X)) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases h_int : (x : X) ∈ interior (A : Set X)
    · exact Or.inl h_int
    · exact Or.inr ⟨hx, h_int⟩
  · intro x hx
    cases hx with
    | inl h_int =>
        -- `x` lies in `interior A`, hence in `A` and thus in `closure A`.
        have hA : (x : X) ∈ (A : Set X) := interior_subset h_int
        exact subset_closure hA
    | inr h_cl =>
        exact h_cl.1