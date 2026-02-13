

theorem P1_Union_finite {X : Type*} [TopologicalSpace X] {A : Finset (Set X)} (h : ∀ s ∈ A, P1 s) : P1 (⋃ s ∈ A, s) := by
  classical
  intro x hx
  -- Extract the witness set `S` with `S ∈ A` and `x ∈ S`.
  rcases Set.mem_iUnion.1 hx with ⟨S, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hS_mem, hxS⟩
  -- Apply the hypothesis `h` to `S`.
  have hx_cl : x ∈ closure (interior S) := (h S hS_mem) hxS
  -- `S` is contained in the big union, hence so is `interior S`.
  have hS_subset :
      S ⊆ ⋃ T ∈ (A : Set (Set X)), (T : Set X) := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨S, ?_⟩
    refine Set.mem_iUnion.2 ⟨hS_mem, hy⟩
  -- Monotonicity of `interior` and `closure`.
  have h_subset :
      closure (interior S) ⊆
        closure (interior (⋃ T ∈ (A : Set (Set X)), (T : Set X))) := by
    apply closure_mono
    apply interior_mono
    exact hS_subset
  exact h_subset hx_cl

theorem P2_Union_finite {X : Type*} [TopologicalSpace X] {A : Finset (Set X)} (h : ∀ s ∈ A, P2 s) : P2 (⋃ s ∈ A, s) := by
  classical
  intro x hx
  -- Find the particular set `S` of the finite union that contains `x`.
  rcases Set.mem_iUnion.1 hx with ⟨S, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hS_mem, hxS⟩
  -- Apply `P2` to `S`.
  have hx_in : x ∈ interior (closure (interior S)) := (h S hS_mem) hxS
  -- `S` is contained in the whole union.
  have hS_subset :
      (S : Set X) ⊆ ⋃ T ∈ (A : Set (Set X)), (T : Set X) := by
    intro y hy
    apply Set.mem_iUnion.2
    refine ⟨S, ?_⟩
    apply Set.mem_iUnion.2
    exact ⟨hS_mem, hy⟩
  -- Monotonicity of `interior` and `closure` gives the desired inclusion.
  have h_subset :
      interior (closure (interior S)) ⊆
        interior (closure (interior (⋃ T ∈ (A : Set (Set X)), (T : Set X)))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    exact hS_subset
  exact h_subset hx_in