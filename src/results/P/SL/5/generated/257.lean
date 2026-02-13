

theorem closure_interior_diff_subset_closure_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (A : Set X) \ interior B := by
  -- `interior (A \ B)` is contained in `A \ B`.
  have h₁ : (interior (A \ B : Set X) : Set X) ⊆ A \ B :=
    interior_subset
  -- Taking closures preserves inclusions.
  have h₂ : closure (interior (A \ B : Set X)) ⊆ closure (A \ B) :=
    closure_mono h₁
  -- From an existing lemma we have `closure (A \ B) ⊆ closure A \ interior B`.
  have h₃ :
      closure (A \ B : Set X) ⊆ closure (A : Set X) \ interior B :=
    closure_diff_subset (A := A) (B := B)
  -- Combine the two inclusions.
  exact h₂.trans h₃