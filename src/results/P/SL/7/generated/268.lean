

theorem Topology.interior_inter_open_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) :
    interior (A ∩ B : Set X) = A ∩ interior B := by
  ext x
  constructor
  · intro hx
    -- `x` lies in `A`.
    have hxA : (x : X) ∈ A :=
      ((interior_subset : interior (A ∩ B) ⊆ A ∩ B) hx).1
    -- `x` lies in `interior B`.
    have hxIntB : x ∈ interior B := by
      have hSub : interior (A ∩ B : Set X) ⊆ interior B :=
        interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
      exact hSub hx
    exact ⟨hxA, hxIntB⟩
  · intro hx
    rcases hx with ⟨hxA, hxIntB⟩
    -- The open set used for the maximality argument.
    have hOpen : IsOpen (A ∩ interior B) :=
      hA.inter isOpen_interior
    -- `A ∩ interior B` is contained in `A ∩ B`.
    have hSub : (A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact ⟨hy.1, (interior_subset : interior B ⊆ B) hy.2⟩
    -- Hence it is contained in the interior of `A ∩ B`.
    have hIncl : (A ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
      interior_maximal hSub hOpen
    exact hIncl ⟨hxA, hxIntB⟩