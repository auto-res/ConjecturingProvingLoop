

theorem interior_prod_subset_interior_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    (interior A) ×ˢ (interior B) ⊆ interior (A ×ˢ B) := by
  intro p hp
  -- `interior A ×ˢ interior B` is open.
  have hOpen : IsOpen ((interior A) ×ˢ (interior B)) :=
    (isOpen_interior).prod isOpen_interior
  -- It is contained in `A ×ˢ B`.
  have hSub : ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ A ×ˢ B := by
    intro q hq
    exact ⟨(interior_subset hq.1), (interior_subset hq.2)⟩
  -- Apply `interior_maximal`.
  exact interior_maximal hSub hOpen hp