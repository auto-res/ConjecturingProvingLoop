

theorem P2_subset_P3 {A : Set X} (h : P2 A) : P3 A := by
  exact subset_trans h (interior_mono (closure_mono interior_subset))

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  -- We must prove `(A ∪ B) ⊆ closure (interior (A ∪ B))`
  intro x hx
  cases hx with
  | inl hAx =>
      -- `x` comes from `A`
      have hxA : x ∈ closure (interior A) := hA hAx
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact h_subset hxA
  | inr hBx =>
      -- `x` comes from `B`
      have hxB : x ∈ closure (interior B) := hB hBx
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact h_subset hxB

theorem P1_closed_of_P2 {A : Set X} (h : P2 A) (hcl : IsClosed A) : P1 A := by
  exact subset_trans h interior_subset

theorem P2_of_closure_eq {A : Set X} (h_eq : closure A = interior A) : P2 A := by
  intro x hx
  have hx_closure : (x : X) ∈ closure A := subset_closure hx
  have hx_int : (x : X) ∈ interior A := by
    simpa [h_eq] using hx_closure
  have h_subset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  exact h_subset hx_int

theorem P2_open {A : Set X} (h_open : IsOpen A) : P2 A := by
  intro x hx
  -- Since `A` is open, it is an open neighbourhood of `x`
  -- that is contained in `closure A`.
  have h₁ : x ∈ interior (closure A) := by
    exact (mem_interior.mpr ⟨A, subset_closure, h_open, hx⟩)
  simpa [h_open.interior_eq] using h₁

theorem interior_subset_of_P1 {A : Set X} (h : P1 A) : interior A ⊆ interior (closure A) := by
  exact interior_mono subset_closure