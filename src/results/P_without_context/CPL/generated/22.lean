

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2 x hxA
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx

theorem P1_closure_eq {A : Set X} (hA : P1 A) : closure (interior A) = closure A := by
  apply le_antisymm
  ·
    exact closure_mono interior_subset
  ·
    have hsub : closure A ⊆ closure (closure (interior A)) := closure_mono hA
    simpa [closure_closure] using hsub

theorem P3_of_ClosureOpen {A : Set X} (hA : IsOpen (closure A)) : P3 A := by
  intro x hx
  have h_cl : x ∈ closure A := subset_closure hx
  have h_nhds : closure A ∈ 𝓝 x := hA.mem_nhds h_cl
  exact (mem_interior_iff_mem_nhds).2 h_nhds

theorem P1_Union_of_P1 {ι : Type*} {A : ι → Set X} (h : ∀ i, P1 (A i)) : P1 (⋃ i, A i) := by
  intro x hx_union
  rcases Set.mem_iUnion.1 hx_union with ⟨i, hxAi⟩
  have hx_cl : x ∈ closure (interior (A i)) := (h i) hxAi
  have h_int_mono : interior (A i) ⊆ interior (⋃ j, A j) := by
    have h_subset : (A i) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono h_subset
  have h_cl_mono :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_int_mono
  exact h_cl_mono hx_cl