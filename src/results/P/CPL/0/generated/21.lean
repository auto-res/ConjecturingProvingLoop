

theorem P1_inter_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ A ∩ closure (interior A) = A := by
  classical
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    · intro x hx
      exact hx.1
    · intro x hxA
      exact ⟨hxA, hP1 hxA⟩
  · intro hEq
    exact (Set.inter_eq_left).1 hEq

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, P2 (s i)) → P2 (⋃ i, s i) := by
  intro hP2
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hP2i : P2 (s i) := hP2 i
  have hx_int : x ∈ interior (closure (interior (s i))) := hP2i hx_i
  have h_subset :
      interior (closure (interior (s i)))
        ⊆ interior (closure (interior (⋃ j, s j))) := by
    -- Step 1: `interior (s i) ⊆ interior (⋃ j, s j)`
    have h_int_sub : interior (s i) ⊆ interior (⋃ j, s j) := by
      have h_sub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_sub
    -- Step 2: take closures
    have h_cl_sub :
        closure (interior (s i))
          ⊆ closure (interior (⋃ j, s j)) :=
      closure_mono h_int_sub
    -- Step 3: take interiors again
    exact interior_mono h_cl_sub
  exact h_subset hx_int