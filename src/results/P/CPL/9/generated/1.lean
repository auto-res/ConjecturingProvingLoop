

theorem union_P2 {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x ∈ A`
      have hxA : x ∈ interior (closure (interior A)) := hA hA_mem
      have h_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- first enlarge the set inside `interior`
        have h_closure :
            closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          -- enlarge the set inside `closure`
          have h_int : interior A ⊆ interior (A ∪ B) := by
            -- enlarge the set inside `interior`
            have h_set : (A : Set X) ⊆ A ∪ B := by
              intro y hy
              exact Or.inl hy
            exact interior_mono h_set
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxA
  | inr hB_mem =>
      -- `x ∈ B`
      have hxB : x ∈ interior (closure (interior B)) := hB hB_mem
      have h_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_closure :
            closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          have h_int : interior B ⊆ interior (A ∪ B) := by
            have h_set : (B : Set X) ⊆ A ∪ B := by
              intro y hy
              exact Or.inr hy
            exact interior_mono h_set
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxB

theorem union_P3 {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x ∈ A`
      have hxA : x ∈ interior (closure A) := hA hA_mem
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have h_closure : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact interior_mono h_closure
      exact h_subset hxA
  | inr hB_mem =>
      -- `x ∈ B`
      have hxB : x ∈ interior (closure B) := hB hB_mem
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have h_closure : closure B ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact interior_mono h_closure
      exact h_subset hxB

theorem P1_interior {A : Set X} : P1 (interior A) := by
  intro x hx
  simpa [interior_interior] using
    (subset_closure hx : x ∈ closure (interior A))