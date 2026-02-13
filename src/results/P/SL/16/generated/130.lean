

theorem Topology.inter_interior_subset_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∩ interior B ⊆ interior (A ∩ B) := by
  intro x hx
  have hOpen : IsOpen (interior A ∩ interior B) :=
    (isOpen_interior.inter isOpen_interior)
  have h_subset : interior A ∩ interior B ⊆ A ∩ B := by
    intro y hy
    exact And.intro (interior_subset hy.1) (interior_subset hy.2)
  have h : interior A ∩ interior B ⊆ interior (A ∩ B) :=
    interior_maximal h_subset hOpen
  exact h hx