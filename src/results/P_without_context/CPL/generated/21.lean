

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  simpa [P1] using (Set.empty_subset _)

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  have h : (Set.univ : Set X) ⊆ interior (closure (Set.univ : Set X)) := by
    simp
  simpa [P3] using h

theorem P1_Union {X : Type*} [TopologicalSpace X] {ι : Sort _} (s : ι → Set X) : (∀ i, P1 (s i)) → P1 (⋃ i, s i) := by
  intro h
  dsimp [P1] at h ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_cl : x ∈ closure (interior (s i)) := h i hxi
  have hint : interior (s i) ⊆ interior (⋃ j, s j) := by
    apply interior_mono
    exact Set.subset_iUnion _ i
  have hcl : closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) :=
    closure_mono hint
  exact hcl hx_cl

theorem P2_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P1]
  intro x hx
  have h : x ∈ interior (closure (interior A)) := hP2 hx
  exact interior_subset h

theorem closure_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : closure A = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    have hclosed : IsClosed (closure (interior A)) := isClosed_closure
    exact closure_minimal h hclosed
  ·
    exact closure_mono interior_subset

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P3]
  intro x hx
  have hx_in : x ∈ interior (closure (interior A)) := hP2 hx
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono interior_subset
  exact h_subset hx_in