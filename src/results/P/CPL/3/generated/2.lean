

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x` comes from `A`
      have hx_closure : x ∈ closure (interior A) := hA hA_mem
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact h_subset hx_closure
  | inr hB_mem =>
      -- `x` comes from `B`
      have hx_closure : x ∈ closure (interior B) := hB hB_mem
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_right
      exact h_subset hx_closure

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hx_in : x ∈ interior (closure (interior A)) := hA hA_mem
      have h_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact h_subset hx_in
  | inr hB_mem =>
      have hx_in : x ∈ interior (closure (interior B)) := hB hB_mem
      have h_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_right
      exact h_subset hx_in

theorem P2_subset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  intro x hxA
  have hx_in : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    apply closure_mono
    exact interior_subset
  exact h_subset hx_in

theorem P3_open {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) : P3 A := by
  intro x hxA
  -- Since `A` is open, its interior is itself.
  have h_eq : interior A = A := h_open.interior_eq
  -- `interior A` is contained in `interior (closure A)` because `A ⊆ closure A`.
  have h_subset : interior A ⊆ interior (closure A) := by
    apply interior_mono
    exact subset_closure
  -- The desired conclusion follows from the two facts above.
  have hx_interiorA : x ∈ interior A := by
    simpa [h_eq] using hxA
  exact h_subset hx_interiorA