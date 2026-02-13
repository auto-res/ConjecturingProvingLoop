

theorem exists_dense_P2_subset_univ {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, P2 A ∧ closure A = Set.univ := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using (P2_univ (X := X))
  · simp [closure_univ]

theorem P1_sigma_family {ι X : Type*} [TopologicalSpace ι] [TopologicalSpace X] {A : ι → Set X} : (∀ i, P1 (A i)) → P1 {p : Σ i, X | p.2 ∈ A p.1} := by
  intro hP1
  -- Define the total set once and for all.
  let S : Set (Σ i : ι, X) := {p | p.2 ∈ A p.1}
  intro p hp
  -- Decompose the point `p`.
  rcases p with ⟨i, x⟩
  -- Translate `hp`.
  have hxA : x ∈ A i := by
    simpa [S] using hp
  ------------------------------------------------------------------
  -- Goal:  `⟨i , x⟩ ∈ closure (interior S)`.
  ------------------------------------------------------------------
  have : (⟨i, x⟩ : Σ i, X) ∈ closure (interior S) := by
    -- Use the neighbourhood-closure criterion.
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    --------------------------------------------------------------
    -- Slice the neighbourhood `U` along the fixed index `i`.
    --------------------------------------------------------------
    let V : Set X := {y | (⟨i, y⟩ : Σ i, X) ∈ U}
    have hVopen : IsOpen V := by
      -- `U` is an open subset of a `Σ`-type, hence each slice is open.
      have hSlices := (isOpen_sigma_iff).1 hUopen
      simpa [V] using hSlices i
    have hxV : x ∈ V := by
      -- Because `⟨i , x⟩ ∈ U`.
      simpa [V] using hxU
    --------------------------------------------------------------
    -- Apply `P1` in the fibre to reach the interior of `A i`.
    --------------------------------------------------------------
    have hx_cl : x ∈ closure (interior (A i)) := (hP1 i) hxA
    -- Therefore `V ∩ interior (A i)` is non-empty.
    have h_nonempty : (V ∩ interior (A i)).Nonempty := by
      have hmem := (mem_closure_iff).1 hx_cl
      exact hmem V hVopen hxV
    rcases h_nonempty with ⟨y, hyV, hyIntA⟩
    --------------------------------------------------------------
    -- Build a point in `U ∩ interior S`.
    --------------------------------------------------------------
    let q : Σ i, X := ⟨i, y⟩
    have hqU : (q : Σ i, X) ∈ U := by
      simpa [V, q] using hyV
    -- Auxiliary open set living inside `S`.
    let T : Set (Σ i, X) := {p : Σ i, X | p.2 ∈ interior (A p.1)}
    have hTopen : IsOpen T := by
      refine (isOpen_sigma_iff).2 ?_
      intro j
      simpa [T] using (isOpen_interior : IsOpen (interior (A j)))
    have hqT : (q : Σ i, X) ∈ T := by
      dsimp [T, q] at *
      exact hyIntA
    -- `T ⊆ S`.
    have hTsub : (T : Set (Σ i, X)) ⊆ S := by
      intro r hr
      dsimp [T, S] at hr ⊢
      exact interior_subset hr
    -- Hence `q` lies in the interior of `S`.
    have hqIntS : (q : Σ i, X) ∈ interior S := by
      have h_nhds : (T : Set (Σ i, X)) ∈ 𝓝 q := hTopen.mem_nhds hqT
      have h_nhds' : (S : Set (Σ i, X)) ∈ 𝓝 q :=
        Filter.mem_of_superset h_nhds hTsub
      exact (mem_interior_iff_mem_nhds).2 h_nhds'
    -- Provide the witness required by the closure criterion.
    exact ⟨q, hqU, hqIntS⟩
  -- Re-express `S`.
  simpa [S] using this