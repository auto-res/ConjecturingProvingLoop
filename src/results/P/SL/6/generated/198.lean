

theorem closure_interiors_subset_closure_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∩ interior B)
      ⊆ closure (interior (A ∩ B)) := by
  -- First, show that `interior A ∩ interior B ⊆ interior (A ∩ B)`.
  have hSub :
      ((interior (A : Set X)) ∩ interior B : Set X) ⊆
        interior (A ∩ B) := by
    intro x hx
    -- `interior A ∩ interior B` is an open set contained in `A ∩ B`.
    have hOpen : IsOpen ((interior (A : Set X)) ∩ interior B) :=
      (isOpen_interior).inter isOpen_interior
    have hIncl :
        ((interior (A : Set X)) ∩ interior B : Set X) ⊆ (A ∩ B) := by
      intro y hy
      exact
        And.intro
          ((interior_subset : interior A ⊆ A) hy.1)
          ((interior_subset : interior B ⊆ B) hy.2)
    -- Apply `interior_maximal` to place `x` in `interior (A ∩ B)`.
    have : x ∈ interior (A ∩ B) :=
      (interior_maximal hIncl hOpen) hx
    exact this
  -- Finally, lift the inclusion through `closure`.
  exact closure_mono hSub