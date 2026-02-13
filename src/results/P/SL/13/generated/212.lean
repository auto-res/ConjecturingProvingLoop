

theorem Topology.compl_closure_inter_self_nonempty_iff {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (((closure (A : Set X))ᶜ) ∩ A : Set X).Nonempty ↔ False := by
  constructor
  · intro hne
    rcases hne with ⟨x, ⟨hx_not_cl, hxA⟩⟩
    have : (x : X) ∈ closure (A : Set X) := subset_closure hxA
    exact hx_not_cl this
  · intro hFalse
    cases hFalse