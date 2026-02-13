

theorem closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `closure (A ∩ interior B)` is contained in `closure A`
  have hxA : x ∈ closure A := by
    have h₁ : A ∩ interior B ⊆ A := Set.inter_subset_left
    have h₂ : closure (A ∩ interior B) ⊆ closure A := closure_mono h₁
    exact h₂ hx
  -- `closure (A ∩ interior B)` is contained in `closure B`
  have hxB : x ∈ closure B := by
    -- First, note that `A ∩ interior B ⊆ B`
    have h₁ : A ∩ interior B ⊆ B := by
      intro y hy
      exact interior_subset hy.2
    -- Taking closures preserves the inclusion
    have h₂ : closure (A ∩ interior B) ⊆ closure B := closure_mono h₁
    exact h₂ hx
  exact And.intro hxA hxB