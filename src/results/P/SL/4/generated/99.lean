

theorem union_interior_closure_interior_subset_interior_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A ⊆ interior (A ∪ B)` by monotonicity of `interior`.
      have h_int_subset :
          interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Taking closures preserves the inclusion.
      have h_closure_subset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      -- Taking interiors again preserves the inclusion.
      have h_int_closure_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_closure_subset
      exact h_int_closure_subset hxA
  | inr hxB =>
      -- Symmetric case for `B`.
      have h_int_subset :
          interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have h_closure_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      have h_int_closure_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_closure_subset
      exact h_int_closure_subset hxB