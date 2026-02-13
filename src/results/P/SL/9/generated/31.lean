

theorem closure_diff_subset {X : Type*} [TopologicalSpace X] (s t : Set X) :
    closure (s \ t) ⊆ closure s \ interior t := by
  intro x hx
  -- `x` lies in the closure of `s`
  have hx_cl_s : x ∈ closure s := by
    have h_sub : s \ t ⊆ s := by
      intro y hy
      exact hy.1
    exact closure_mono h_sub hx
  -- `x` is not in the interior of `t`
  have hx_not_int : x ∉ interior t := by
    by_contra hx_int
    -- Any neighbourhood of `x` meets `s \\ t`; pick `interior t`
    have h_nonempty : ((interior t) ∩ (s \ t)).Nonempty := by
      have h_closure := (mem_closure_iff).1 hx
      exact h_closure _ isOpen_interior hx_int
    rcases h_nonempty with ⟨y, ⟨hy_int_t, hy_diff⟩⟩
    have : y ∈ t := interior_subset hy_int_t
    exact hy_diff.2 this
  exact ⟨hx_cl_s, hx_not_int⟩