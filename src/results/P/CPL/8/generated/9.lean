

theorem P1_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P3 A → P1 A := by
  intro hClosed hP3
  have hP2 : P2 A := (P2_iff_P3_of_closed (X := X) (A := A) hClosed).2 hP3
  exact P2_to_P1 (A := A) hP2

theorem P2_unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} : (∀ i, P2 (A i)) → P2 (⋃ i, A i) := by
  intro hP2
  intro x hx
  -- Obtain an index `i` such that `x ∈ A i`.
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  -- Apply `P2` for `A i`.
  have hP2i : P2 (A i) := hP2 i
  have hx_in : x ∈ interior (closure (interior (A i))) := hP2i hxAi
  -- Relate the relevant interiors/closures to those of the big union.
  have hsubset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    -- `interior (A i)` is contained in `interior (⋃ j, A j)`.
    have h1 : interior (A i) ⊆ interior (⋃ j, A j) := by
      have hAisub : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hAisub
    -- Take closures, then interiors again.
    have h2 : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
      closure_mono h1
    exact interior_mono h2
  exact hsubset hx_in

theorem P3_unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} : (∀ i, P3 (A i)) → P3 (⋃ i, A i) := by
  intro hP3
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hP3i : P3 (A i) := hP3 i
  have hx_int : x ∈ interior (closure (A i)) := hP3i hxAi
  have hsubset : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    have hAi_sub : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    have h_closure : closure (A i) ⊆ closure (⋃ j, A j) :=
      closure_mono hAi_sub
    exact interior_mono h_closure
  exact hsubset hx_int