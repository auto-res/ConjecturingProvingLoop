

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} (h : ∀ i, P1 (s i)) : P1 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_closure : x ∈ closure (interior (s i)) := (h i) hx_i
  have h_subset :
      closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) := by
    apply closure_mono
    apply interior_mono
    exact Set.subset_iUnion _ i
  exact h_subset hx_closure

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hx_in : x ∈ interior (closure A) := hA hA_mem
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_left
      exact h_subset hx_in
  | inr hB_mem =>
      have hx_in : x ∈ interior (closure B) := hB hB_mem
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_right
      exact h_subset hx_in

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ P1 A ∧ P3 A := by
  constructor
  · intro hP2
    exact ⟨P2_subset_P1 hP2, P2_subset_P3 hP2⟩
  · rintro ⟨hP1, hP3⟩
    -- We show `P2 A`.
    intro x hxA
    -- From `hP1` we obtain the equality of closures.
    have h_eq : closure (interior A) = closure A := (P1_iff_eq).1 hP1
    -- Using `hP3`, `x` lies in `interior (closure A)`.
    have hx_in : x ∈ interior (closure A) := hP3 hxA
    -- Rewriting with the equality gives the desired conclusion.
    simpa [h_eq] using hx_in