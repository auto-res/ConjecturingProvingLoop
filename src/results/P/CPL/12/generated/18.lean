

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (Set.prod A B) := by
  -- Unpack a point of `A ×ˢ B`
  rintro ⟨x, y⟩ hxy
  rcases hxy with ⟨hxA, hyB⟩
  -- Use the `P1` hypotheses for the two coordinates
  have hx_cl : x ∈ closure (interior (A : Set X)) := hA hxA
  have hy_cl : y ∈ closure (interior (B : Set Y)) := hB hyB
  -- We prove that `(x, y)` lies in the closure of the interior of `A ×ˢ B`
  apply (mem_closure_iff).2
  intro W hWopen hWmem
  -- A neighbourhood of `(x, y)` in the product gives rectangle neighbourhoods
  have hW_nhds : (W : Set (X × Y)) ∈ 𝓝 (x, y) :=
    IsOpen.mem_nhds hWopen hWmem
  rcases (mem_nhds_prod_iff).1 hW_nhds with
    ⟨U, hU_nhds, V, hV_nhds, hUVsub⟩
  -- Shrink to open sets `U₀ ⊆ U`, `V₀ ⊆ V`
  rcases (mem_nhds_iff).1 hU_nhds with
    ⟨U₀, hU₀_sub, hU₀_open, hxU₀⟩
  rcases (mem_nhds_iff).1 hV_nhds with
    ⟨V₀, hV₀_sub, hV₀_open, hyV₀⟩
  -- Use the closure conditions to pick points in the interiors
  have h_nonempty_x :
      (U₀ ∩ interior (A : Set X)).Nonempty :=
    (mem_closure_iff).1 hx_cl U₀ hU₀_open hxU₀
  rcases h_nonempty_x with ⟨x', hx'inter⟩
  have hxU₀' : (x' : X) ∈ U₀ := hx'inter.1
  have hx'Int : x' ∈ interior (A : Set X) := hx'inter.2
  have h_nonempty_y :
      (V₀ ∩ interior (B : Set Y)).Nonempty :=
    (mem_closure_iff).1 hy_cl V₀ hV₀_open hyV₀
  rcases h_nonempty_y with ⟨y', hy'inter⟩
  have hyV₀' : (y' : Y) ∈ V₀ := hy'inter.1
  have hy'Int : y' ∈ interior (B : Set Y) := hy'inter.2
  -- Show that `(x', y')` lies in `W`
  have h_in_W : (x', y') ∈ W := by
    have hxU : (x' : X) ∈ U := hU₀_sub hxU₀'
    have hyV : (y' : Y) ∈ V := hV₀_sub hyV₀'
    have h_in_UV : (x', y') ∈ U ×ˢ V := by
      exact ⟨hxU, hyV⟩
    exact hUVsub h_in_UV
  ------------------------------------------------------------------
  -- `interior A ×ˢ interior B` is contained in `interior (A ×ˢ B)`
  ------------------------------------------------------------------
  have h_subset_int :
      ((interior (A : Set X)) ×ˢ (interior (B : Set Y))) ⊆
        interior ((A : Set X) ×ˢ (B : Set Y)) := by
    -- The product of open sets is open
    have h_open :
        IsOpen (((interior (A : Set X))) ×ˢ (interior (B : Set Y))) :=
      (isOpen_interior).prod isOpen_interior
    -- It is contained in `A ×ˢ B`
    have h_sub :
        ((interior (A : Set X)) ×ˢ (interior (B : Set Y))) ⊆
          (A : Set X) ×ˢ (B : Set Y) := by
      intro p hp
      rcases hp with ⟨h1, h2⟩
      exact ⟨interior_subset h1, interior_subset h2⟩
    exact interior_maximal h_sub h_open
  -- Hence `(x', y')` lies in the interior of `A ×ˢ B`
  have h_in_int :
      (x', y') ∈ interior ((A : Set X) ×ˢ (B : Set Y)) :=
    h_subset_int ⟨hx'Int, hy'Int⟩
  -- Produce the required point in the intersection `W ∩ interior (A ×ˢ B)`
  exact ⟨(x', y'), And.intro h_in_W h_in_int⟩