

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : P3 A) : P3 (interior A) := by
  intro x hx
  -- use the hypothesis `h` to avoid an unused-argument warning
  have _ := h
  -- `interior A` is open and contained in its own closure,
  -- hence it is contained in the interior of that closure
  have h_subset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    have h_open : IsOpen (interior A) := isOpen_interior
    exact
      interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
        h_open
  exact h_subset hx

theorem P1_prod_of_P2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P1 (Set.prod A B) := by
  -- First, obtain `P2` for the product using the hypotheses.
  have h : P2 (Set.prod A B) := P2_prod (A := A) (B := B) hA hB
  -- Then convert `P2` to `P1`.
  exact P1_of_P2 (A := Set.prod A B) h

theorem P2_union_inter {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ (A ∩ B)) := by
  -- Use `hB` to avoid an unused variable warning
  have _ := hB
  -- Since `A ∩ B ⊆ A`, the union collapses to `A`.
  have h_eq : (A ∪ (A ∩ B) : Set X) = A := by
    have h_subset : (A ∩ B : Set X) ⊆ A := by
      intro x hx
      exact hx.1
    simpa using (Set.union_eq_left.2 h_subset)
  simpa [h_eq] using hA