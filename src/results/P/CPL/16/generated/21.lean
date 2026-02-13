

theorem P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∩ B) := by
  intro hA hB
  -- unfold the definition of `P2`
  unfold P2 at hA hB ⊢
  intro x hx
  -- split the membership of `x`
  have hxA : x ∈ A := hx.1
  have hxB : x ∈ B := hx.2
  -- the two regular–open supersets coming from the hypotheses
  have hx_rA : x ∈ interior (closure (interior A)) := hA hxA
  have hx_rB : x ∈ interior (closure (interior B)) := hB hxB
  -- define the open set `U`
  let U : Set X := interior (closure (interior A)) ∩ interior (closure (interior B))
  have hU_open : IsOpen (U : Set X) := (isOpen_interior).inter isOpen_interior
  have hxU : x ∈ (U : Set X) := by
    dsimp [U] at *
    exact ⟨hx_rA, hx_rB⟩
  -- show `U ⊆ closure (interior (A ∩ B))`
  have hUsubset : (U : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro z hz
    have hz_rA : z ∈ interior (closure (interior A)) := hz.1
    have hz_rB : z ∈ interior (closure (interior B)) := hz.2
    -- neighbourhood characterization of the closure
    apply (mem_closure_iff).2
    intro V hV hzV
    -- Step 1 : meet `interior A`
    have h_open₁ : IsOpen (V ∩ interior (closure (interior B))) :=
      hV.inter isOpen_interior
    have hz_open₁ : z ∈ V ∩ interior (closure (interior B)) := ⟨hzV, hz_rB⟩
    have hz_clA : z ∈ closure (interior A) := (interior_subset) hz_rA
    have h_nonempty₁ :
        ((V ∩ interior (closure (interior B))) ∩ interior A).Nonempty := by
      have h := (mem_closure_iff).1 hz_clA _ h_open₁ hz_open₁
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h
    rcases h_nonempty₁ with ⟨w₁, ⟨⟨hw₁V, hw₁_rB⟩, hw₁_intA⟩⟩
    -- Step 2 : meet `interior B`
    have hw₁_clB : w₁ ∈ closure (interior B) := (interior_subset) hw₁_rB
    have h_open₂ : IsOpen (V ∩ interior A) := hV.inter isOpen_interior
    have hw₁_open₂ : w₁ ∈ V ∩ interior A := ⟨hw₁V, hw₁_intA⟩
    have h_nonempty₂ : ((V ∩ interior A) ∩ interior B).Nonempty := by
      have h := (mem_closure_iff).1 hw₁_clB _ h_open₂ hw₁_open₂
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h
    rcases h_nonempty₂ with ⟨w, ⟨⟨hwV, hw_intA⟩, hw_intB⟩⟩
    -- `w` belongs to `interior (A ∩ B)`
    have hw_intAB : w ∈ interior (A ∩ B) := by
      -- an open neighbourhood contained in `A ∩ B`
      have hOpen : IsOpen (interior A ∩ interior B) :=
        (isOpen_interior).inter isOpen_interior
      have hSub : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
        intro t ht
        exact ⟨(interior_subset) ht.1, (interior_subset) ht.2⟩
      have hIncl := interior_maximal hSub hOpen
      exact hIncl ⟨hw_intA, hw_intB⟩
    exact ⟨w, hwV, hw_intAB⟩
  -- `x` lies in the open set `U`, which is contained in the desired set
  have : x ∈ interior (closure (interior (A ∩ B))) := by
    have hIncl := interior_maximal hUsubset hU_open
    exact hIncl hxU
  exact this

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    · -- `closure (interior A)` is contained in `closure A`
      exact closure_mono interior_subset
    · -- `closure A` is contained in `closure (interior A)` since `A ⊆ closure (interior A)`
      exact closure_minimal hP1 isClosed_closure
  · intro hEq
    -- rewrite `subset_closure` using the given equality
    have h : (A : Set X) ⊆ closure A := subset_closure
    simpa [hEq.symm] using h