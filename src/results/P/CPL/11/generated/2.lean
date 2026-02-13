

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure A) := hA hxA
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have hcl : closure A ⊆ closure (A ∪ B) :=
          closure_mono (by
            intro y hy
            exact Or.inl hy)
        exact interior_mono hcl
      exact hsubset hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure B) := hB hxB
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have hcl : closure B ⊆ closure (A ∪ B) :=
          closure_mono (by
            intro y hy
            exact Or.inr hy)
        exact interior_mono hcl
      exact hsubset hxB'

theorem exists_open_dense_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, ?_⟩
  · -- `A ⊆ U`
    exact hA
  · -- `closure U = closure A`
    apply le_antisymm
    · -- `closure U ⊆ closure A`
      have h₁ : (interior (closure A) : Set X) ⊆ closure A :=
        interior_subset
      have h₂ : closure (interior (closure A)) ⊆ closure A := by
        simpa [closure_closure] using closure_mono h₁
      exact h₂
    · -- `closure A ⊆ closure U`
      have h₁ : (A : Set X) ⊆ interior (closure A) := hA
      have h₂ : closure A ⊆ closure (interior (closure A)) := by
        simpa using closure_mono h₁
      exact h₂