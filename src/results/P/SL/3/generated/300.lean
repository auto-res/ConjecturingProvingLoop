

theorem closure_diff_eq_self_inter_compl {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) \ A = closure (A : Set X) ∩ (A : Set X)ᶜ := by
  rfl