

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  exact False.elim hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem exists_open_dense_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  -- We take `U = interior (closure (interior A))`
  refine ⟨interior (closure (interior A)), isOpen_interior, ?_, ?_⟩
  · -- `A ⊆ U`
    exact hA
  · -- `closure U = closure A`
    apply le_antisymm
    · -- `closure U ⊆ closure A`
      have h₁ : (interior (closure (interior A)) : Set X) ⊆ closure A := by
        intro x hx
        -- From `hx : x ∈ U` we get `x ∈ closure (interior A)`
        have hx' : x ∈ closure (interior A) :=
          (interior_subset :
            interior (closure (interior A)) ⊆ closure (interior A)) hx
        -- And `closure (interior A) ⊆ closure A`
        have hcl :
            (closure (interior A) : Set X) ⊆ closure A :=
          closure_mono (interior_subset : (interior A : Set X) ⊆ A)
        exact hcl hx'
      have : closure (interior (closure (interior A))) ⊆ closure A := by
        simpa [closure_closure] using closure_mono h₁
      exact this
    · -- `closure A ⊆ closure U`
      have h₂ : (A : Set X) ⊆ interior (closure (interior A)) := hA
      have : closure A ⊆ closure (interior (closure (interior A))) :=
        closure_mono h₂
      simpa using this

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : P1 (closure A) := by
  intro x hx
  -- We first prove that `closure A ⊆ closure (interior (closure A))`.
  have hsubset : (closure A : Set X) ⊆ closure (interior (closure A)) := by
    -- It suffices to show `A ⊆ closure (interior (closure A))`
    -- and then use `closure_minimal`.
    have hA' : (A : Set X) ⊆ closure (interior (closure A)) := by
      intro y hy
      -- From `P1 A` we know `y ∈ closure (interior A)`.
      have hy₁ : y ∈ closure (interior A) := hA hy
      -- Since `A ⊆ closure A`, we have `interior A ⊆ interior (closure A)`.
      have hint : (interior A : Set X) ⊆ interior (closure A) :=
        interior_mono (subset_closure : (A : Set X) ⊆ closure A)
      -- Taking closures preserves inclusion.
      have hcl : (closure (interior A) : Set X) ⊆ closure (interior (closure A)) :=
        closure_mono hint
      exact hcl hy₁
    -- Apply the universal property of the closure.
    exact closure_minimal hA' isClosed_closure
  exact hsubset hx