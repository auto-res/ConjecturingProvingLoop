

theorem interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∩ interior B ⊆ interior (A ∩ B : Set X) := by
  intro x hx
  -- `interior A` and `interior B` are open.
  have hOpen : IsOpen (interior A ∩ interior B) :=
    (isOpen_interior).inter isOpen_interior
  -- Their intersection is contained in `A ∩ B`.
  have hSub : (interior A ∩ interior B : Set X) ⊆ (A ∩ B) := by
    intro y hy
    exact And.intro (interior_subset hy.1) (interior_subset hy.2)
  -- By maximality of the interior, the intersection is contained in
  -- `interior (A ∩ B)`.
  have hIncl : (interior A ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
    interior_maximal hSub hOpen
  exact hIncl hx