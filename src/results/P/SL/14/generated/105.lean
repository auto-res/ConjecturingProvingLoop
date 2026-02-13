

theorem Topology.closureInterior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A` is contained in `interior (A ∪ B)`.
      have h_int_mono : interior A ⊆ interior (A ∪ B) := by
        have h_subset : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact interior_mono h_subset
      -- Taking closures preserves the inclusion.
      have h_closure_mono : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_mono
      exact h_closure_mono hxA
  | inr hxB =>
      -- `interior B` is contained in `interior (A ∪ B)`.
      have h_int_mono : interior B ⊆ interior (A ∪ B) := by
        have h_subset : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact interior_mono h_subset
      -- Taking closures preserves the inclusion.
      have h_closure_mono : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_mono
      exact h_closure_mono hxB