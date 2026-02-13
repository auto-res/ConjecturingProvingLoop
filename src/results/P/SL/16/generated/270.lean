

theorem Topology.union_interior_closure_interior_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Step 1: `interior A ⊆ interior (A ∪ B)`
      have h_int_subset : interior A ⊆ interior (A ∪ B) := by
        have h_sub : A ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact interior_mono h_sub
      -- Step 2: `closure (interior A) ⊆ closure (interior (A ∪ B))`
      have h_closure_subset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      -- Step 3: apply `interior_mono`
      have h_int_closure_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_closure_subset
      exact h_int_closure_subset hxA
  | inr hxB =>
      -- The same three steps with `B` instead of `A`.
      have h_int_subset : interior B ⊆ interior (A ∪ B) := by
        have h_sub : B ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact interior_mono h_sub
      have h_closure_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      have h_int_closure_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_closure_subset
      exact h_int_closure_subset hxB