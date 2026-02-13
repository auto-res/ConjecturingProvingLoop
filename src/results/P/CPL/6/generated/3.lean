

theorem P2_of_open {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hxA
  have h_mem_nhds : (closure A : Set X) ∈ 𝓝 x := by
    have hA_nhds : (A : Set X) ∈ 𝓝 x := hA.mem_nhds hxA
    exact Filter.mem_of_superset hA_nhds (subset_closure : (A : Set X) ⊆ closure A)
  have hx_int : x ∈ interior (closure A) := (mem_interior_iff_mem_nhds).2 h_mem_nhds
  simpa [hA.interior_eq] using hx_int

theorem P3_iUnion {ι : Sort*} {A : ι → Set X} (h : ∀ i, P3 (A i)) : P3 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxAi⟩
  have hx1 : x ∈ interior (closure (A i)) := (h i) hxAi
  have hsubset : closure (A i) ⊆ closure (⋃ j, A j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  exact (interior_mono hsubset) hx1