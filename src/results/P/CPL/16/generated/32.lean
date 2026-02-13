

theorem P1_sUnion_of_closed {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, IsClosed A ∧ P1 A) → P1 (⋃₀ 𝒜) := by
  intro h
  apply P1_sUnion
  intro A hA
  exact (h A hA).2

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 A → P3 B → P3 (Set.prod A B) := by
  intro hA hB
  -- Unfold the definitions of `P3`
  unfold P3 at hA hB ⊢
  intro p hp
  -- Split the components of the point `p`
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Use the hypotheses `P3 A` and `P3 B`
  have hx : x ∈ interior (closure A) := hA hxA
  have hy : y ∈ interior (closure B) := hB hyB
  -- Consider the product of the two open sets
  let S : Set (X × Y) := Set.prod (interior (closure A)) (interior (closure B))
  have hS_open : IsOpen (S : Set (X × Y)) :=
    (isOpen_interior).prod isOpen_interior
  have hpS : (x, y) ∈ S := by
    dsimp [S] at *
    exact ⟨hx, hy⟩
  -- Show that `S ⊆ closure (A ×ˢ B)`
  have hS_subset : (S : Set (X × Y)) ⊆ closure (Set.prod A B) := by
    intro z hz
    -- Split `z`
    rcases z with ⟨u, v⟩
    dsimp [S] at hz
    rcases hz with ⟨hu_int, hv_int⟩
    have hu_cl : u ∈ closure A := interior_subset hu_int
    have hv_cl : v ∈ closure B := interior_subset hv_int
    -- Show `(u, v)` lies in the closure of `A × B`
    have : (u, v) ∈ closure (Set.prod A B) := by
      -- Use the neighbourhood characterization of the closure
      apply (mem_closure_iff).2
      intro W hW hWuv
      -- Obtain a rectangular neighbourhood contained in `W`
      have hW_nhds : (W : Set (X × Y)) ∈ nhds (u, v) := IsOpen.mem_nhds hW hWuv
      rcases (mem_nhds_prod_iff).1 hW_nhds with
        ⟨U, hU_nhds, V, hV_nhds, hUV_sub⟩
      -- Refine the neighbourhoods around `u` and `v`
      rcases (mem_nhds_iff).1 hU_nhds with
        ⟨U₀, hU₀_sub, hU₀_open, huU₀⟩
      rcases (mem_nhds_iff).1 hV_nhds with
        ⟨V₀, hV₀_sub, hV₀_open, hvV₀⟩
      -- `U₀` meets `A`
      have hA_nonempty : (U₀ ∩ A).Nonempty := by
        have := (mem_closure_iff).1 hu_cl U₀ hU₀_open huU₀
        simpa using this
      rcases hA_nonempty with ⟨a, haU₀, haA⟩
      -- `V₀` meets `B`
      have hB_nonempty : (V₀ ∩ B).Nonempty := by
        have := (mem_closure_iff).1 hv_cl V₀ hV₀_open hvV₀
        simpa using this
      rcases hB_nonempty with ⟨b, hbV₀, hbB⟩
      -- The pair `(a, b)` is in `W`
      have habW : (a, b) ∈ W := by
        have : (a, b) ∈ Set.prod U V := by
          exact ⟨hU₀_sub haU₀, hV₀_sub hbV₀⟩
        exact hUV_sub this
      -- And `(a, b)` is in `A × B`
      have hab_prod : (a, b) ∈ Set.prod A B := by
        exact ⟨haA, hbB⟩
      exact ⟨(a, b), ⟨habW, hab_prod⟩⟩
    simpa using this
  -- Apply `interior_maximal`
  have hxy : (x, y) ∈ interior (closure (Set.prod A B)) :=
    (interior_maximal hS_subset hS_open) hpS
  exact hxy