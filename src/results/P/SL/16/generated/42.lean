

theorem Topology.closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have h_int_subset : interior A ⊆ interior (A ∪ B) := by
        have h_sub : A ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact interior_mono h_sub
      have h_closure_subset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      exact h_closure_subset hxA
  | inr hxB =>
      have h_int_subset : interior B ⊆ interior (A ∪ B) := by
        have h_sub : B ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact interior_mono h_sub
      have h_closure_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      exact h_closure_subset hxB