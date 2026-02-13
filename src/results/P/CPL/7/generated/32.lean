

theorem exists_closure_subset_open_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : ∃ U, IsOpen U ∧ closure U ⊆ closure A ∧ A ⊆ closure U := by
  refine ⟨interior A, isOpen_interior, ?_, ?_⟩
  ·
    have : closure (interior A : Set X) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa using this
  ·
    simpa using hA

theorem P1_prod_univ {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (A ×ˢ (Set.univ : Set Y)) := by
  have hUniv : Topology.P1 (Set.univ : Set Y) := P1_univ
  simpa using P1_prod (A := A) (B := (Set.univ : Set Y)) hA hUniv

theorem P1_Union_finite {X : Type*} [TopologicalSpace X] {F : Finset (Set X)} (hF : ∀ A, A ∈ F → Topology.P1 A) : Topology.P1 (⋃ A ∈ F, A) := by
  classical
  revert hF
  induction F using Finset.induction with
  | empty =>
      intro _hF
      simpa using (P1_empty : Topology.P1 (∅ : Set X))
  | @insert A s hA_notin_s ih =>
      intro hF
      -- `P1` for the distinguished set `A`
      have hA : Topology.P1 A := by
        have : (A : Set X) ∈ (insert A s : Finset (Set X)) :=
          Finset.mem_insert_self A s
        exact hF A this
      -- `P1` for the union over the remaining sets, from the induction hypothesis
      have hF' : ∀ B, B ∈ s → Topology.P1 B := by
        intro B hB
        exact hF B (Finset.mem_insert_of_mem hB)
      have h_s : Topology.P1 (⋃ B ∈ s, (B : Set X)) := ih hF'
      -- Combine the two using `P1_union`
      have h_union : Topology.P1 (A ∪ ⋃ B ∈ s, (B : Set X)) :=
        P1_union hA h_s
      -- Relate the two ways of writing the union
      have h_eq :
          (⋃ B ∈ (insert A s : Finset (Set X)), (B : Set X)) =
            (A ∪ ⋃ B ∈ s, (B : Set X)) := by
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨B, hx₁⟩
          rcases Set.mem_iUnion.1 hx₁ with ⟨hBmem, hxB⟩
          have h_cases : (B : Set X) = A ∨ (B : Set X) ∈ s :=
            (Finset.mem_insert).1 hBmem
          cases h_cases with
          | inl hBA =>
              left
              simpa [hBA] using hxB
          | inr hBinS =>
              right
              have : x ∈ ⋃ B ∈ s, (B : Set X) := by
                apply Set.mem_iUnion.2
                refine ⟨B, ?_⟩
                apply Set.mem_iUnion.2
                exact ⟨hBinS, hxB⟩
              exact this
        · intro hx
          cases hx with
          | inl hxA =>
              apply Set.mem_iUnion.2
              refine ⟨A, ?_⟩
              apply Set.mem_iUnion.2
              exact ⟨Finset.mem_insert_self A s, hxA⟩
          | inr hxUnion =>
              rcases Set.mem_iUnion.1 hxUnion with ⟨B, hx₁⟩
              rcases Set.mem_iUnion.1 hx₁ with ⟨hBmem, hxB⟩
              apply Set.mem_iUnion.2
              refine ⟨B, ?_⟩
              apply Set.mem_iUnion.2
              exact ⟨Finset.mem_insert_of_mem hBmem, hxB⟩
      simpa [h_eq] using h_union