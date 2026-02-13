

theorem interior_interiors_subset_interior_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ∩ interior B ⊆ interior (A ∩ B) := by
  intro x hx
  -- `interior A ∩ interior B` is an open set …
  have h_open :
      IsOpen (interior (A : Set X) ∩ interior B) :=
    (isOpen_interior : IsOpen (interior (A : Set X))).inter
      (isOpen_interior : IsOpen (interior B))
  -- … contained in `A ∩ B`.
  have h_subset :
      (interior (A : Set X) ∩ interior B : Set X) ⊆ A ∩ B := by
    intro y hy
    exact ⟨interior_subset hy.1, interior_subset hy.2⟩
  -- By maximality of the interior, it is contained in `interior (A ∩ B)`.
  have h_contained :
      (interior (A : Set X) ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
    interior_maximal h_subset h_open
  exact h_contained hx