

theorem Topology.interior_inter_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) = interior A ∩ interior B := by
  -- First, establish the inclusion `⊆`.
  have h₁ :
      interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
    intro x hx
    have hxA : x ∈ interior A :=
      (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
    have hxB : x ∈ interior B :=
      (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
    exact And.intro hxA hxB
  -- Next, establish the inclusion `⊇`.
  have h₂ :
      interior A ∩ interior B ⊆ interior (A ∩ B : Set X) := by
    -- The set `interior A ∩ interior B` is open …
    have h_open : IsOpen (interior A ∩ interior B : Set X) :=
      (isOpen_interior : IsOpen (interior A)).inter
        (isOpen_interior : IsOpen (interior B))
    -- … and contained in `A ∩ B`.
    have h_sub :
        (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro x hx
      exact And.intro
        ((interior_subset : interior A ⊆ A) hx.1)
        ((interior_subset : interior B ⊆ B) hx.2)
    -- Hence it is contained in the interior of `A ∩ B`.
    exact interior_maximal h_sub h_open
  -- Combine the two inclusions into an equality.
  exact Set.Subset.antisymm h₁ h₂