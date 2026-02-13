

theorem interior_closure_iUnion_subset
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, interior (closure (A i : Set X))) ⊆
      interior (closure (⋃ i, A i : Set X)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `interior` and `closure` are both monotone, allowing us to enlarge the set.
  have hIncl :
      interior (closure (A i : Set X)) ⊆
        interior (closure (⋃ j, A j : Set X)) := by
    apply interior_mono
    have hSub : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact closure_mono hSub
  exact hIncl hx_i