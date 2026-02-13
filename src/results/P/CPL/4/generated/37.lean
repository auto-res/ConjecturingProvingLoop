

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} (h : Topology.P1 (closure (A ∪ B))) : Topology.P1 (closure A ∪ closure B) := by
  dsimp [Topology.P1] at h ⊢
  intro x hx
  -- View `x` as a point of `closure (A ∪ B)`
  have hx_cl : x ∈ closure (A ∪ B) := by
    simpa [closure_union] using hx
  -- Apply the hypothesis `h`
  have hx_in : x ∈ closure (interior (closure (A ∪ B))) := h hx_cl
  -- Rewrite back using `closure_union`
  simpa [closure_union] using hx_in

theorem P1_iff_closure_eq_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure A = closure (interior A) := by
  simpa [eq_comm] using
    (P1_iff_closure_interior_eq_closure (X := X) (A := A))

theorem P3_iUnion_finite {X : Type*} [TopologicalSpace X] {s : Finset (Set X)} (h : ∀ A ∈ s, Topology.P3 A) : Topology.P3 (⋃ A ∈ s, A) := by
  classical
  -- Unfold the definition of `P3`
  dsimp [Topology.P3]
  -- Take a point of the big union
  intro x hxU
  /- 1.  Choose a particular set `A ∈ s` that contains `x`. -/
  rcases Set.mem_iUnion.1 hxU with ⟨A, hxU₁⟩
  rcases Set.mem_iUnion.1 hxU₁ with ⟨hA_mem, hxA⟩
  /- 2.  `A` itself satisfies `P3`. -/
  have hA_P3 : (A : Set X) ⊆ interior (closure A) :=
    h A hA_mem
  have hx₁ : x ∈ interior (closure A) := hA_P3 hxA
  /- 3.  Monotonicity:  
         `interior (closure A) ⊆ interior (closure ⋃ B ∈ s, B)`. -/
  -- First: `A ⊆ ⋃ B ∈ s, B`
  have hA_subset_union : (A : Set X) ⊆ ⋃ B ∈ s, B := by
    intro y hy
    -- Build the membership in the double `iUnion`
    apply Set.mem_iUnion.2
    refine ⟨A, ?_⟩
    apply Set.mem_iUnion.2
    exact ⟨hA_mem, hy⟩
  -- Taking closures then interiors
  have h_closure_subset :
      (closure A : Set X) ⊆ closure (⋃ B ∈ s, B) :=
    closure_mono hA_subset_union
  have h_interior_closure_subset :
      interior (closure A) ⊆
        interior (closure (⋃ B ∈ s, B)) :=
    interior_mono h_closure_subset
  /- 4.  Finish. -/
  exact h_interior_closure_subset hx₁

theorem P2_of_open_neighborhoods {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior (closure (interior A))) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  obtain ⟨U, _hUopen, hxU, hU_subset⟩ := h x hxA
  have hx_closure : (x : X) ∈ closure U := subset_closure hxU
  exact hU_subset hx_closure