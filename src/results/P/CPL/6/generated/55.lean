

theorem P1_sdiff_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X} : IsClosed B → Topology.P1 A → Topology.P1 (A \ B) := by
  intro hClosedB hP1A
  intro x hxAB
  -- Decompose the hypothesis `x ∈ A \ B`.
  have hxA : x ∈ A := hxAB.1
  have hxNotB : x ∉ B := hxAB.2
  -- From `P1 A`, we know `x ∈ closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hP1A hxA
  -- We will use the neighbourhood characterisation of `closure`.
  have h_intA :
      ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ interior A).Nonempty :=
    (mem_closure_iff).1 hx_cl
  -- Goal: every neighbourhood of `x` meets `interior (A \ B)`.
  have h_goal :
      ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ interior (A \ B)).Nonempty := by
    intro U hU hxU
    -- Work inside the open set `U ∩ Bᶜ`.
    have hOpen_comp : IsOpen (Bᶜ) := hClosedB.isOpen_compl
    have hV_open : IsOpen (U ∩ Bᶜ) := hU.inter hOpen_comp
    have hxV : x ∈ U ∩ Bᶜ := by
      exact ⟨hxU, by
        -- `x ∈ Bᶜ` since `x ∉ B`.
        simpa using hxNotB⟩
    -- Apply the closure property of `interior A`.
    have h_nonempty := h_intA (U ∩ Bᶜ) hV_open hxV
    rcases h_nonempty with ⟨z, ⟨hzU, hzBcomp⟩, hzIntA⟩
    -- Show that `z ∈ interior (A \ B)`.
    have hzIntAB : (z : X) ∈ interior (A \ B) := by
      -- `interior A` and `Bᶜ` are open.
      have hOpen_intA : IsOpen (interior A) := isOpen_interior
      have hOpen_int : IsOpen (interior A ∩ Bᶜ) :=
        hOpen_intA.inter hOpen_comp
      -- `z` lies in this open set.
      have hz_mem : z ∈ interior A ∩ Bᶜ := ⟨hzIntA, hzBcomp⟩
      -- This open set is contained in `A \ B`.
      have h_subset :
          (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
        intro w hw
        exact ⟨interior_subset hw.1, hw.2⟩
      -- Use the neighbourhood criterion for `interior`.
      have h_nhds :
          (interior A ∩ Bᶜ : Set X) ∈ 𝓝 z :=
        hOpen_int.mem_nhds hz_mem
      have h_nhds' : (A \ B : Set X) ∈ 𝓝 z :=
        Filter.mem_of_superset h_nhds h_subset
      exact (mem_interior_iff_mem_nhds).2 h_nhds'
    -- `z` witnesses the required non‐emptiness.
    exact ⟨z, ⟨hzU, hzIntAB⟩⟩
  -- Apply the neighbourhood characterisation to conclude.
  exact (mem_closure_iff).2 h_goal