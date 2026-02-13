

theorem Topology.interior_inter_open_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) :
    interior (A ∩ B : Set X) = A ∩ interior B := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx_intB : x ∈ interior B :=
      (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
    have hx_AB : x ∈ (A ∩ B : Set X) := interior_subset hx
    exact And.intro hx_AB.1 hx_intB
  · intro x hx
    rcases hx with ⟨hxA, hx_intB⟩
    -- The set `A ∩ interior B` is open and contains `x`
    have h_open : IsOpen (A ∩ interior B) := hA.inter isOpen_interior
    have h_subset : (A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact And.intro hy.1 (interior_subset hy.2)
    have hx_mem : x ∈ (A ∩ interior B : Set X) := And.intro hxA hx_intB
    exact
      mem_interior.2
        ⟨A ∩ interior B, h_subset, h_open, hx_mem⟩