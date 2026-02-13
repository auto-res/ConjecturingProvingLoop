

theorem closure_interior_eq_of_P2 {A : Set X} (h : P2 A) : closure (interior A) = closure A := by
  apply le_antisymm
  ·
    exact closure_mono interior_subset
  ·
    -- First, upgrade the hypothesis `h` to `A ⊆ closure (interior A)`
    have hA : (A : Set X) ⊆ closure (interior A) := by
      intro x hx
      have : x ∈ interior (closure (interior A)) := h hx
      exact interior_subset this
    -- Then take closures of both sides
    have : closure A ⊆ closure (interior A) := by
      simpa [closure_closure] using (closure_mono hA)
    exact this

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  unfold P1 at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ closure (interior A) := hA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono
            (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact h_subset hxA'
  | inr hxB =>
      have hxB' : x ∈ closure (interior B) := hB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono
            (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact h_subset hxB'

theorem exists_P1_P2_P3 : ∃ (A : Set X), P1 A ∧ P2 A ∧ P3 A := by
  refine ⟨(∅ : Set X), ?_, ?_, ?_⟩
  all_goals
    intro x hx
    cases hx

theorem P1_self_closure_interior {A : Set X} : P1 (closure (interior A)) := by
  -- Unfold the definition of `P1`
  unfold P1
  intro x hx
  -- First, show `interior A ⊆ interior (closure (interior A))`
  have h_interior_subset :
      (interior A : Set X) ⊆ interior (closure (interior A)) := by
    -- `interior_mono` gives the desired inclusion after noting
    -- `interior A ⊆ closure (interior A)`
    have h :
        interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono (by
        intro y hy
        exact subset_closure hy)
    -- Since `interior (interior A) = interior A`, we rewrite
    simpa [isOpen_interior.interior_eq] using h
  -- Take closures of both sides of the inclusion obtained above
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono h_interior_subset
  -- Apply the inclusion to the given element
  exact h_closure_subset hx