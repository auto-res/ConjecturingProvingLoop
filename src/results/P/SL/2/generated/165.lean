

theorem Topology.nonempty_of_interior_closure_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (interior (closure (A : Set X))).Nonempty → A.Nonempty := by
  classical
  intro hInt
  -- First, record that the closure of `A` is nonempty.
  have hCl : (closure (A : Set X)).Nonempty := by
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, interior_subset hxInt⟩
  -- We prove the goal by contradiction.
  by_contra hA
  -- From the assumption `¬ A.Nonempty`, deduce that `A = ∅`.
  have hAeq : (A : Set X) = ∅ := by
    simpa [Set.not_nonempty_iff_eq_empty] using hA
  -- Hence the closure of `A` is also empty.
  have hClEq : closure (A : Set X) = (∅ : Set X) := by
    simpa [hAeq] using closure_empty
  -- But `hCl` provides a point in the (empty) closure, a contradiction.
  rcases hCl with ⟨x, hxCl⟩
  have : (x : X) ∈ (∅ : Set X) := by
    simpa [hClEq] using hxCl
  cases this