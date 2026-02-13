

theorem interior_iInter_subset_iInter_interior
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    interior (Set.iInter A) ⊆ Set.iInter (fun i => interior (A i)) := by
  classical
  intro x hx
  rcases (Set.mem_interior).1 hx with ⟨U, hU_open, hU_sub, hxU⟩
  apply Set.mem_iInter.2
  intro i
  have hU_sub_i : U ⊆ A i := by
    intro y hy
    have h_mem : y ∈ Set.iInter A := hU_sub hy
    exact (Set.mem_iInter.1 h_mem) i
  exact
    (Set.mem_interior).2 ⟨U, hU_open, hU_sub_i, hxU⟩