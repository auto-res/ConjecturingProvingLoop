

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono (interior_subset : interior A ⊆ A))
  exact fun x hx => hsubset (hP2 hx)

theorem P1_iff_closure_eq_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    have h₂ : closure A ⊆ closure (interior A) :=
      closure_minimal hP1 isClosed_closure
    exact subset_antisymm h₁ h₂
  · intro hEq
    have h : A ⊆ closure (interior A) := by
      intro x hx
      have : (x ∈ closure A) := subset_closure hx
      simpa [hEq] using this
    exact h

theorem P2_iUnion {X ι : Type*} [TopologicalSpace X] (s : ι → Set X) (h : ∀ i, P2 (s i)) : P2 (⋃ i, s i) := by
  intro x hx
  rcases (Set.mem_iUnion.1 hx) with ⟨i, hxi⟩
  -- `x` is in `s i`, hence in the target interior for `s i`
  have hmem : x ∈ interior (closure (interior (s i))) := (h i) hxi
  -- establish the chain of inclusions needed
  have h_sub_int : interior (s i) ⊆ interior (⋃ j, s j) :=
    interior_mono (Set.subset_iUnion (fun j => s j) i)
  have h_sub_cl :
      closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) :=
    closure_mono h_sub_int
  have h_sub :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) :=
    interior_mono h_sub_cl
  exact h_sub hmem