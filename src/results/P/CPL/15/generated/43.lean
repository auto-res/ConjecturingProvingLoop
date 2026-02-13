

theorem P2_subset_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : A ⊆ closure (interior (closure A)) := by
  intro x hxA
  -- Step 1: from `P2`, place `x` in `interior (closure (interior A))`.
  have hx₁ : x ∈ interior (closure (interior A)) := h hxA
  -- Step 2: the interior is contained in its own closure.
  have hx₂ : x ∈ closure (interior (closure (interior A))) :=
    subset_closure hx₁
  -- Step 3: compare the two closures.
  have h_subset :
      (closure (interior (closure (interior A))) : Set X) ⊆
        closure (interior (closure A)) := by
    -- First, relate the interiors.
    have h_inner :
        (interior (closure (interior A)) : Set X) ⊆
          interior (closure A) := by
      -- `closure (interior A) ⊆ closure A`
      have h_closure :
          (closure (interior A) : Set X) ⊆ closure A :=
        closure_mono (interior_subset : (interior A : Set X) ⊆ A)
      exact interior_mono h_closure
    -- Take closures of both sides.
    exact closure_mono h_inner
  -- Step 4: conclude.
  exact h_subset hx₂