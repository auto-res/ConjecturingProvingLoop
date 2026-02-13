

theorem closure_subset_of_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (A : Set X) ⊆ interior (closure (B : Set X))) :
    closure (A : Set X) ⊆ closure (B : Set X) := by
  -- First, upgrade the inclusion to one into `closure B`.
  have h₁ : (A : Set X) ⊆ closure (B : Set X) :=
    Set.Subset.trans h interior_subset
  -- Taking closures preserves inclusions.
  have h₂ :
      closure (A : Set X) ⊆ closure (closure (B : Set X)) :=
    closure_mono h₁
  -- Simplify `closure (closure B)` to `closure B`.
  simpa [closure_closure] using h₂