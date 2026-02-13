

theorem Topology.interiorClosure_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `closure A ⊆ closure (A ∪ B)`
      have h_closure_mono : closure A ⊆ closure (A ∪ B) := by
        have : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact closure_mono this
      -- Taking interiors preserves the inclusion.
      have h_int_mono : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure_mono
      exact h_int_mono hxA
  | inr hxB =>
      -- `closure B ⊆ closure (A ∪ B)`
      have h_closure_mono : closure B ⊆ closure (A ∪ B) := by
        have : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact closure_mono this
      -- Taking interiors preserves the inclusion.
      have h_int_mono : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure_mono
      exact h_int_mono hxB