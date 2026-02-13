

theorem Topology.interior_closure_interior_union_subset {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ interior (closure (interior A))`.
      have h_subset : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        -- First, upgrade the inclusion from interiors to closures.
        have h_closure : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          -- Since `A ⊆ A ∪ B`, we obtain `interior A ⊆ interior (A ∪ B)`.
          have h_int : interior A ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
          -- Taking closures preserves this inclusion.
          exact closure_mono h_int
        -- Passing to interiors yields the desired inclusion.
        exact interior_mono h_closure
      exact h_subset hxA
  | inr hxB =>
      -- Handle the symmetric case `x ∈ interior (closure (interior B))`.
      have h_subset : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h_closure : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          have h_int : interior B ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxB