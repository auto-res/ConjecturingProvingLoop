

theorem P2_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hxA
  -- Since `A` is open, its interior is itself.
  have h_eq : interior A = A := hA.interior_eq
  -- Hence `x` belongs to `interior A`.
  have hx_intA : x ∈ interior A := by
    simpa [h_eq] using hxA
  -- `interior A` is open and contained in `closure (interior A)`,
  -- so it is contained in `interior (closure (interior A))`.
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  -- Finish the proof.
  exact h_subset hx_intA

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure (interior A) = Set.univ) : P1 A := by
  intro x hx
  simpa [h_dense] using (Set.mem_univ x)

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure (interior A) = Set.univ) : P2 A := by
  intro x hx
  simpa [h_dense, interior_univ] using (Set.mem_univ x)

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (A ∪ B ∪ C) := by
  have hAB : P1 (A ∪ B) := P1_union hA hB
  simpa using P1_union hAB hC