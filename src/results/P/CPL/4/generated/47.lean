

theorem P3_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : IsClosed B) : Topology.P3 (A \ B) := by
  -- Unfold the definition of `P3`
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  -- `hx` splits into membership of `A` and non–membership of `B`
  have hxA : x ∈ A := hx.1
  have hxNotB : x ∈ Bᶜ := by
    simpa using hx.2
  -- From `P3 A` we get that `x` lies in `interior (closure A)`
  have hx_int_clA : x ∈ interior (closure A) := hA hxA
  ------------------------------------------------------------------
  -- An auxiliary open neighbourhood avoiding `B`
  ------------------------------------------------------------------
  set U : Set X := interior (closure A) ∩ Bᶜ with hU_def
  have hU_open : IsOpen U :=
    (isOpen_interior : IsOpen (interior (closure A))).inter hB.isOpen_compl
  have hxU : x ∈ U := by
    simpa [hU_def] using And.intro hx_int_clA hxNotB
  ------------------------------------------------------------------
  -- Show that `U` is contained in `closure (A \ B)`
  ------------------------------------------------------------------
  have hU_subset : (U : Set X) ⊆ closure (A \ B) := by
    intro y hy
    have hy_int_clA : y ∈ interior (closure A) := hy.1
    have hyNotB : y ∈ Bᶜ := hy.2
    have hy_clA : y ∈ closure A := interior_subset hy_int_clA
    -- Prove that `y` belongs to the closure of `A \ B`
    have : y ∈ closure (A \ B) := by
      -- Use the neighbourhood characterisation of the closure
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- Intersect the neighbourhood with `Bᶜ` (still open & contains `y`)
      have hWopen : IsOpen (V ∩ Bᶜ) := hVopen.inter hB.isOpen_compl
      have hyW : y ∈ V ∩ Bᶜ := And.intro hyV hyNotB
      -- Since `y ∈ closure A`, this intersection meets `A`
      have h_nonempty :=
        (mem_closure_iff).1 hy_clA (V ∩ Bᶜ) hWopen hyW
      rcases h_nonempty with ⟨z, hz⟩
      rcases hz with ⟨hzVB, hzA⟩
      rcases hzVB with ⟨hzV, hzNotB⟩
      -- The witness lies in `A \ B` and in `V`
      exact ⟨z, And.intro hzV ⟨hzA, hzNotB⟩⟩
    exact this
  ------------------------------------------------------------------
  -- Maximality of the interior gives the desired conclusion
  ------------------------------------------------------------------
  have : x ∈ interior (closure (A \ B)) :=
    (interior_maximal hU_subset hU_open) (by
      simpa [hU_def] using hxU)
  exact this

theorem P3_interior_compl {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P3 A) : Topology.P3 (interior Aᶜ) := by
  simpa using
    (openSet_P3 (X := X) (A := interior (Aᶜ)) isOpen_interior)