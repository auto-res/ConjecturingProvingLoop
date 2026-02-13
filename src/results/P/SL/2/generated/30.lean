

theorem Topology.P1_nonempty_implies_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior A).Nonempty := by
  intro hP1 hA_nonempty
  rcases hA_nonempty with ⟨x, hxA⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  by_cases hIntEq : interior A = ∅
  ·
    have hFalse : False := by
      simpa [hIntEq, closure_empty] using hx_cl
    exact hFalse.elim
  ·
    classical
    exact Set.nonempty_iff_ne_empty.mpr hIntEq