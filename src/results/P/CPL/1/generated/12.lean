

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : P1 (closure A) := by
  intro x hx
  -- First, rewrite `closure (interior A)` using `P1 A`.
  have h_eq : (closure (interior A) : Set X) = closure A :=
    closure_interior_eq_of_P1 (A := A) h
  -- View `x` as an element of `closure (interior A)`.
  have hx' : x ∈ closure (interior A) := by
    simpa [h_eq] using hx
  -- Show the required inclusion of closures.
  have h_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (closure A)) := by
    -- Since `A ⊆ closure A`, we have `interior A ⊆ interior (closure A)`.
    have h_int :
        (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    -- Taking closures preserves the inclusion.
    exact closure_mono h_int
  exact h_subset hx'

theorem P1_iff_P2_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  refine ⟨fun _ => P2_of_isOpen (A := A) hA,
         fun _ => P1_of_isOpen (A := A) hA⟩

theorem P2_Union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : P2 A) (hB : P2 B) (hC : P2 C) (hD : P2 D) : P2 (A ∪ B ∪ C ∪ D) := by
  -- Step 1: obtain `P2` for `A ∪ B`
  have hAB : P2 (A ∪ B) :=
    P2_union (A := A) (B := B) hA hB
  -- Step 2: obtain `P2` for `A ∪ B ∪ C`
  have hABC : P2 (A ∪ B ∪ C) := by
    have : P2 ((A ∪ B) ∪ C) :=
      P2_union (A := (A ∪ B)) (B := C) hAB hC
    simpa [Set.union_assoc] using this
  -- Step 3: obtain `P2` for `A ∪ B ∪ C ∪ D`
  have hABCD : P2 (A ∪ B ∪ C ∪ D) := by
    have : P2 ((A ∪ B ∪ C) ∪ D) :=
      P2_union (A := (A ∪ B ∪ C)) (B := D) hABC hD
    simpa [Set.union_assoc] using this
  exact hABCD