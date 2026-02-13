

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} (h : ∀ i, P3 (s i)) : P3 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- from `P3 (s i)` we know `x` lies in `interior (closure (s i))`
  have hx' : x ∈ interior (closure (s i)) := (h i) hx_i
  -- we now relate this interior to the desired one
  have h_subset : interior (closure (s i)) ⊆ interior (closure (⋃ j, s j)) := by
    have h_closure : closure (s i) ⊆ closure (⋃ j, s j) := by
      refine closure_mono ?_
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono h_closure
  exact h_subset hx'

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} (h : ∀ i, P2 (s i)) : P2 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx' : x ∈ interior (closure (interior (s i))) := (h i) hx_i
  have h_subset :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) := by
    have h_closure :
        closure (interior (s i)) ⊆
          closure (interior (⋃ j, s j)) := by
      have h_sub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      have h_int : (interior (s i) : Set X) ⊆ interior (⋃ j, s j) :=
        interior_mono h_sub
      exact closure_mono h_int
    exact interior_mono h_closure
  exact h_subset hx'

theorem exists_dense_open_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ U, IsOpen U ∧ closure U = closure A ∧ U ⊆ A := by
  refine ⟨interior A, isOpen_interior, ?_, interior_subset⟩
  simpa using (P1_iff_closure_interior_eq).1 hA