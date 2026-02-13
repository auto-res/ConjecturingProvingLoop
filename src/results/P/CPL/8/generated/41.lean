

theorem P2_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X} : IsOpen B → P2 A → P2 (A ∩ B) := by
  intro hBopen hP2
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- From `P2 A`, obtain a neighbourhood of `x`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Auxiliary open set around `x`.
  set O : Set X := interior (closure (interior A)) ∩ B with hOdef
  have hOopen : IsOpen O := by
    have : IsOpen (interior (closure (interior A))) := isOpen_interior
    have : IsOpen (interior (closure (interior A)) ∩ B) :=
      this.inter hBopen
    simpa [hOdef] using this
  have hxO : x ∈ O := by
    dsimp [O, hOdef]
    exact ⟨hxInt, hxB⟩
  -- Show that `O` is contained in the relevant closure.
  have hOsubset : (O : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro y hyO
    rcases hyO with ⟨hyIntClA, hyB⟩
    have hyClA : y ∈ closure (interior A) := interior_subset hyIntClA
    -- Prove `y ∈ closure (interior (A ∩ B))`.
    have : y ∈ closure (interior (A ∩ B)) := by
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- Refine the neighbourhood with `B`.
      have hVBopen : IsOpen (V ∩ B) := hVopen.inter hBopen
      have hyVB : y ∈ V ∩ B := ⟨hyV, hyB⟩
      -- Use closeness to hit `interior A`.
      have hNonempty : ((V ∩ B) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hyClA (V ∩ B) hVBopen hyVB
      rcases hNonempty with ⟨z, ⟨hzV, hzB⟩, hzIntA⟩
      -- Show the witness lies in `interior (A ∩ B)`.
      have hzIntAB : z ∈ interior (A ∩ B) := by
        -- The open set `interior A ∩ B` sits inside `A ∩ B`.
        have hSub : (interior A ∩ B : Set X) ⊆ interior (A ∩ B) := by
          have hOpen : IsOpen (interior A ∩ B) :=
            isOpen_interior.inter hBopen
          have hIncl : (interior A ∩ B : Set X) ⊆ A ∩ B := by
            intro w hw
            rcases hw with ⟨hwIntA, hwB⟩
            exact ⟨interior_subset hwIntA, hwB⟩
          exact interior_maximal hIncl hOpen
        exact hSub ⟨hzIntA, hzB⟩
      exact ⟨z, hzV, hzIntAB⟩
    exact this
  -- Conclude that `x` is in the desired interior.
  have hNhd : (O : Set X) ∈ 𝓝 x := hOopen.mem_nhds hxO
  have hMem : x ∈ interior (closure (interior (A ∩ B))) :=
    (mem_interior_iff_mem_nhds).2 (Filter.mem_of_superset hNhd hOsubset)
  simpa using hMem

theorem P2_union₂ {X : Type*} [TopologicalSpace X] {ι κ : Sort*} {A : ι → κ → Set X} : (∀ i j, P2 (A i j)) → P2 (⋃ i, ⋃ j, A i j) := by
  intro hAll
  -- First, establish `P2` for `⋃ j, A i j` for each fixed `i`.
  have hP2_i : ∀ i, P2 (⋃ j, A i j) := by
    intro i
    have hP2_ij : ∀ j, P2 (A i j) := by
      intro j
      exact hAll i j
    simpa using (P2_unionᵢ (A := fun j => A i j) hP2_ij)
  -- Then, use `P2_unionᵢ` once more to get the result for the double union.
  simpa using (P2_unionᵢ (A := fun i => ⋃ j, A i j) hP2_i)

theorem P1_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → interior (closure (interior A)) = interior (closure A) := by
  intro hP1
  have hcl : closure (interior (A : Set X)) = closure A :=
    closure_interior_eq_of_P1 (A := A) hP1
  simpa [hcl]