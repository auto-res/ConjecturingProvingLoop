

theorem P2_setdiff {X} [TopologicalSpace X] {A B : Set X} : P2 A → IsClosed B → B ⊆ A → P2 (A \ B) := by
  classical
  intro hP2 hBclosed hBsub
  -- We unfold the definition of `P2 (A \ B)`.
  intro x hxDiff
  rcases hxDiff with ⟨hxA, hxNotB⟩
  -- Step 1: `P2 A` gives us a good open neighbourhood of `x`.
  have hxK : x ∈ interior (closure (interior A)) := hP2 hxA
  have hKopen : IsOpen (interior (closure (interior A))) := isOpen_interior
  -- Step 2: work in the open set `O := K ∩ Bᶜ`.
  let O : Set X := interior (closure (interior A)) ∩ (Bᶜ : Set X)
  have hOopen : IsOpen O :=
    hKopen.inter hBclosed.isOpen_compl
  have hxO : x ∈ O := by
    dsimp [O]
    exact And.intro hxK hxNotB
  ------------------------------------------------------------------
  -- Goal:  `O ⊆ closure (interior (A \ B))`.
  ------------------------------------------------------------------
  have hOsubset : (O : Set X) ⊆ closure (interior (A \ B)) := by
    intro y hyO
    -- Decompose the membership information.
    have hyK    : y ∈ interior (closure (interior A)) := hyO.1
    have hyNotB : y ∉ B := hyO.2
    -- From `hyK` we drop to the closure of `interior A`.
    have hy_cl : y ∈ closure (interior A) := interior_subset hyK
    -- We prove `y ∈ closure (interior (A \ B))` via the neighbourhood
    -- characterisation.
    refine
      (mem_closure_iff).2 ?_
    intro U hUopen hyU
    -- Shrink the neighbourhood so that it avoids `B`.
    have hUopen' : IsOpen (U ∩ (Bᶜ : Set X)) :=
      hUopen.inter hBclosed.isOpen_compl
    have hyU' : y ∈ U ∩ (Bᶜ : Set X) := by
      exact ⟨hyU, hyNotB⟩
    -- Since `y ∈ closure (interior A)`, this set meets `interior A`.
    obtain ⟨z, hzU', hzIntA⟩ :=
      (mem_closure_iff).1 hy_cl _ hUopen' hyU'
    -- Split the information on `z`.
    have hzU : z ∈ U := hzU'.1
    have hzNotB : z ∈ (Bᶜ : Set X) := hzU'.2
    -- Show that `z ∈ interior (A \ B)`.
    have hzIntDiff : z ∈ interior (A \ B) := by
      -- The open set `W := interior A ∩ Bᶜ` contains `z`
      -- and is contained in `A \ B`.
      have hWopen : IsOpen (interior A ∩ (Bᶜ : Set X)) :=
        isOpen_interior.inter hBclosed.isOpen_compl
      have hzW : z ∈ interior A ∩ (Bᶜ : Set X) := ⟨hzIntA, hzNotB⟩
      have hWsub : (interior A ∩ (Bᶜ : Set X) : Set X) ⊆ A \ B := by
        intro w hw
        rcases hw with ⟨hwIntA, hwNotB⟩
        exact ⟨interior_subset hwIntA, hwNotB⟩
      have h_nhds : (A \ B : Set X) ∈ 𝓝 z :=
        Filter.mem_of_superset (hWopen.mem_nhds hzW) hWsub
      exact (mem_interior_iff_mem_nhds).2 h_nhds
    -- Provide the required intersection witness.
    exact ⟨z, ⟨hzU, hzIntDiff⟩⟩
  ------------------------------------------------------------------
  -- Step 3: upgrade via `interior_maximal`.
  ------------------------------------------------------------------
  have hOsubsetInt :
      (O : Set X) ⊆ interior (closure (interior (A \ B))) :=
    interior_maximal hOsubset hOopen
  exact hOsubsetInt hxO