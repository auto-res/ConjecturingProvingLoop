

theorem Topology.frontier_eq_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = closure A ∩ closure (Aᶜ) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx_cl, hx_not_int⟩
    -- `x ∉ interior A` gives membership in the complement of `interior A`
    have h_mem_compl : x ∈ (interior A)ᶜ := by
      simpa using hx_not_int
    -- Rewrite using `closure_compl` to obtain membership in `closure (Aᶜ)`
    have hx_cl_compl : x ∈ closure (Aᶜ) := by
      simpa [closure_compl] using h_mem_compl
    exact And.intro hx_cl hx_cl_compl
  · intro hx
    rcases hx with ⟨hx_clA, hx_clAc⟩
    -- From `x ∈ closure (Aᶜ)` derive `x ∉ interior A`
    have hx_not_int : x ∉ interior A := by
      have h_mem_compl : x ∈ (interior A)ᶜ := by
        simpa [closure_compl] using hx_clAc
      simpa using h_mem_compl
    exact And.intro hx_clA hx_not_int