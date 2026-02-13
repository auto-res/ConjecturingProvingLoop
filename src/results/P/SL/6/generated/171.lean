

theorem iUnion_closure_subset_closure_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (S : ι → Set X) :
    (⋃ i, closure (S i) : Set X) ⊆ closure (⋃ i, S i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `S i` is included in the total union.
  have hSub : (S i : Set X) ⊆ ⋃ j, S j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Since `x ∈ closure (S i)` and `S i ⊆ ⋃ j, S j`,
  -- monotonicity of `closure` yields the desired membership.
  have : x ∈ closure (⋃ j, S j) :=
    (closure_mono hSub) hx_i
  exact this