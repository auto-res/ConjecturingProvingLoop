

theorem Topology.interior_inter_eq_inter_left_of_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  apply Set.Subset.antisymm
  · intro x hx
    -- `x` lies in both `interior A` and `B`
    have hxInt : x ∈ interior A ∩ interior B :=
      (Topology.interior_inter_subset (A := A) (B := B)) hx
    have hxAB : x ∈ (A ∩ B : Set X) :=
      (interior_subset : interior (A ∩ B) ⊆ A ∩ B) hx
    exact And.intro hxInt.1 hxAB.2
  · intro x hx
    -- `interior A ∩ B` is open and contained in `A ∩ B`
    have hSub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    have hOpen : IsOpen (interior A ∩ B) :=
      isOpen_interior.inter hB
    -- Maximal property of the interior
    exact
      (interior_maximal hSub hOpen) hx