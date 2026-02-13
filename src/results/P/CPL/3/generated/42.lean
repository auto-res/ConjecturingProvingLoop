

theorem P2_equiv_P1_closure_open {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen (closure A)) : P2 A ↔ P1 A := by
  constructor
  · intro hP2
    exact P2_subset_P1 (A := A) hP2
  · intro hP1
    exact P2_of_P1_and_open_closure (A := A) hP1 h_open

theorem P3_Union_finite {X : Type*} [TopologicalSpace X] {A : Finset (Set X)} (h : ∀ s ∈ A, P3 s) : P3 (⋃ s ∈ A, s) := by
  classical
  intro x hx
  -- Extract a set `S ∈ A` such that `x ∈ S`.
  rcases Set.mem_iUnion.1 hx with ⟨S, hx₁⟩
  rcases Set.mem_iUnion.1 hx₁ with ⟨hS_mem, hxS⟩
  -- Use the hypothesis `P3 S`.
  have hx_int : x ∈ interior (closure S) := (h S hS_mem) hxS
  -- `S` is included in the big union.
  have hS_subset :
      (S : Set X) ⊆ ⋃ T ∈ (A : Set (Set X)), (T : Set X) := by
    intro y hy
    apply Set.mem_iUnion.2
    refine ⟨S, ?_⟩
    apply Set.mem_iUnion.2
    exact ⟨hS_mem, hy⟩
  -- Monotonicity of `closure` and `interior`.
  have h_subset :
      interior (closure S) ⊆
        interior (closure (⋃ T ∈ (A : Set (Set X)), (T : Set X))) := by
    apply interior_mono
    apply closure_mono
    exact hS_subset
  exact h_subset hx_int