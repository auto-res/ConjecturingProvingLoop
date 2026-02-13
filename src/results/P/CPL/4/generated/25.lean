

theorem P2_iUnion_finite {X : Type*} [TopologicalSpace X] {s : Finset (Set X)} (h : ∀ A ∈ s, Topology.P2 A) : Topology.P2 (⋃ A ∈ s, A) := by
  classical
  -- Unfold the definition of `P2`
  dsimp [Topology.P2]
  -- Take a point of the big union
  intro x hxU
  /- 1.  Choose a particular set `A ∈ s` that contains `x`. -/
  rcases Set.mem_iUnion.1 hxU with ⟨A, hxU₁⟩
  rcases Set.mem_iUnion.1 hxU₁ with ⟨hA_mem, hxA⟩
  /- 2.  `A` itself satisfies `P2`. -/
  have hA_P2 : (A : Set X) ⊆ interior (closure (interior A)) :=
    h A hA_mem
  have hx₁ : x ∈ interior (closure (interior A)) := hA_P2 hxA
  /- 3.  Monotonicity:  
         `interior (closure (interior A)) ⊆
          interior (closure (interior ⋃ B ∈ s, B))`. -/
  -- First: `A ⊆ ⋃ B ∈ s, B`
  have hA_subset_union : (A : Set X) ⊆ ⋃ B ∈ s, B := by
    intro y hy
    -- Build the membership in the double `iUnion`
    apply Set.mem_iUnion.2
    refine ⟨A, ?_⟩
    apply Set.mem_iUnion.2
    exact ⟨hA_mem, hy⟩
  -- Hence `interior A ⊆ interior (⋃ B ∈ s, B)`
  have h_int_subset :
      (interior A : Set X) ⊆ interior (⋃ B ∈ s, B) :=
    interior_mono hA_subset_union
  -- Taking closures then interiors again
  have h_closure_subset :
      (closure (interior A) : Set X) ⊆
        closure (interior (⋃ B ∈ s, B)) :=
    closure_mono h_int_subset
  have h_interior_closure_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃ B ∈ s, B))) :=
    interior_mono h_closure_subset
  /- 4.  Finish. -/
  exact h_interior_closure_subset hx₁

theorem P2_iff_exists_open_between {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ ∃ U, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (interior A)) := by
  constructor
  · intro hP2
    exact P2_exists_open_superset (A := A) hP2
  · rintro ⟨U, _hUopen, hAU, hUsubset⟩
    exact fun x hx => hUsubset (hAU hx)