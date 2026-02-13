

theorem Topology.interior_closure_interior_subset_interior_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure B) := by
  -- First, `interior A ⊆ B` because `interior A ⊆ A` and `A ⊆ B`.
  have h₁ : (interior A : Set X) ⊆ B := by
    intro x hx
    exact hAB (interior_subset hx)
  -- Taking closures preserves this inclusion.
  have h₂ : closure (interior A : Set X) ⊆ closure B := closure_mono h₁
  -- Taking interiors once more yields the desired inclusion.
  exact interior_mono h₂